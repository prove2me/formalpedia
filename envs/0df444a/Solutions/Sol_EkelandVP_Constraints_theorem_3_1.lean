-- Prove2me | solution 1 for EkelandVP.Constraints.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T12:33:38.983003+00:00
-- url     : https://prove2.me/submissions/8a8e56e4-7ece-42b8-baea-13f80e67c3a1

import Mathlib
import Definitions.Def_EkelandVP_Constraints_feasibleSet
import Definitions.Def_EkelandVP_Constraints_IsRegular

-- Complete module: EKProof/SharedBasics.lean

-- Complete module: EKProof/FiniteConstraints.lean

open scoped BigOperators

namespace EkelandVP.Constraints.EKFresh

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype I]

noncomputable def constraintMap (a : I → V →L[ℝ] ℝ) : V →L[ℝ] (I → ℝ) :=
  ContinuousLinearMap.pi a

theorem constraintMap_surjective (a : I → V →L[ℝ] ℝ)
    (ha : LinearIndependent ℝ a) : Function.Surjective (constraintMap a) := by
  classical
  apply LinearMap.dualMap_injective_iff.mp
  apply (injective_iff_map_eq_zero _).mpr
  intro g hg
  let c : I → ℝ := fun i => g (Pi.single i 1)
  have he (y : I → ℝ) : g y = ∑ i, c i * y i := by
    conv_lhs => rw [← Finset.univ_sum_single y]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hs : Pi.single i (y i) = y i • Pi.single i (1 : ℝ) := by
      ext j
      by_cases hj : j = i <;> simp [hj]
    rw [hs, map_smul]
    simp [c, mul_comm]
  have hc : ∑ i, c i • a i = 0 := by
    ext x
    have hx := congrArg (fun q : V →ₗ[ℝ] ℝ => q x) hg
    change g (constraintMap a x) = 0 at hx
    rw [he] at hx
    simpa [constraintMap] using hx
  have hz : ∀ i, c i = 0 := (Fintype.linearIndependent_iff.mp ha) c hc
  ext y
  simp [he, hz]

theorem constraintMap_rightInverse (a : I → V →L[ℝ] ℝ)
    (ha : LinearIndependent ℝ a) :
    ∃ B : (I → ℝ) →L[ℝ] V, ∀ y, constraintMap a (B y) = y := by
  exact ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional
    (constraintMap_surjective a ha)

theorem finite_constraint_factor [DecidableEq I] (a : I → V →L[ℝ] ℝ)
    (B : (I → ℝ) →L[ℝ] V) (hB : ∀ y, constraintMap a (B y) = y)
    (w : V →L[ℝ] ℝ) (hw : ∀ x, constraintMap a x = 0 → w x = 0) :
    w = ∑ i, w (B (Pi.single i 1)) • a i := by
  classical
  ext x
  have hx : w (x - B (constraintMap a x)) = 0 := by
    apply hw
    simp [map_sub, hB]
  have he : w x = w (B (constraintMap a x)) := by
    simpa [map_sub, sub_eq_zero] using hx
  rw [he, ← Finset.univ_sum_single (constraintMap a x), map_sum, map_sum]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hs : Pi.single i (constraintMap a x i) =
      (constraintMap a x i) • Pi.single i (1 : ℝ) := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [hs, map_smul, map_smul]
  simp [constraintMap, mul_comm]

end EkelandVP.Constraints.EKFresh

-- Complete module: EKProof/ImplicitCurve.lean

open Filter
open scoped Topology

namespace EkelandVP.Constraints.EKFresh

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CompleteSpace V] [Fintype I]

omit [CompleteSpace V] in
theorem exists_corrected_curve (G : I → V → ℝ) (hG : ∀ i, ContDiff ℝ 1 (G i))
    (v h : V) (hv : ∀ i, G i v = 0)
    (B : (I → ℝ) →L[ℝ] V)
    (hB : ∀ y, constraintMap (fun i => fderiv ℝ (G i) v) (B y) = y) :
    ∃ u : ℝ → V, u 0 = v ∧ HasDerivAt u h 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, G i (u t) = t * fderiv ℝ (G i) v h := by
  let A := constraintMap (fun i => fderiv ℝ (G i) v)
  let C : (ℝ × (I → ℝ)) →L[ℝ] V :=
    (ContinuousLinearMap.fst ℝ ℝ (I → ℝ)).smulRight h +
      B.comp (ContinuousLinearMap.snd ℝ ℝ (I → ℝ))
  let H : ℝ × (I → ℝ) → (I → ℝ) :=
    fun q i => G i (v + C q) - q.1 * A h i
  have hC : HasStrictFDerivAt (fun q => v + C q) C (0, 0) := by
    simpa using (C.hasStrictFDerivAt.const_add v)
  have hH : HasStrictFDerivAt H (ContinuousLinearMap.snd ℝ ℝ (I → ℝ)) (0, 0) := by
    apply hasStrictFDerivAt_pi''
    intro i
    have hi0 : HasStrictFDerivAt (G i) (fderiv ℝ (G i) v) (v + C (0, 0)) := by
      change HasStrictFDerivAt (G i) (fderiv ℝ (G i) v) (v + C 0)
      simpa using (hG i).hasStrictFDerivAt (x := v) (by norm_num)
    have hi := hi0.comp (0, 0) hC
    have hit := hi.sub (hasStrictFDerivAt_fst.mul_const (A h i))
    convert hit using 1
    · ext q
      simp [H]
    · apply ContinuousLinearMap.ext
      intro q
      have hBi := congrFun (hB q.2) i
      simp only [constraintMap, ContinuousLinearMap.pi_apply] at hBi
      simp [C, A, constraintMap, hBi, mul_comm]
  have hinv : ((ContinuousLinearMap.snd ℝ ℝ (I → ℝ)).comp
      (ContinuousLinearMap.inr ℝ ℝ (I → ℝ))).IsInvertible := by
    exact ⟨ContinuousLinearEquiv.refl ℝ (I → ℝ), by ext q i; rfl⟩
  let z := hH.implicitFunctionOfProdDomain hinv
  have hz0 : z 0 = 0 :=
    (hH.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds.mp rfl
  have hz : HasStrictFDerivAt z (0 : ℝ →L[ℝ] (I → ℝ)) 0 := by
    simpa only [ContinuousLinearMap.snd_comp_inl, ContinuousLinearMap.comp_zero, neg_zero]
      using hH.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv
  let u : ℝ → V := fun t => v + t • h + B (z t)
  refine ⟨u, ?_, ?_, ?_⟩
  · simp [u, hz0]
  · have hu := ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add v
    have hzu : HasDerivAt z 0 0 := by simpa using hz.hasFDerivAt.hasDerivAt
    simpa [u, Pi.add_def, Function.comp_def] using hu.add (B.hasFDerivAt.comp_hasDerivAt 0 hzu)
  · filter_upwards [hH.eventually_apply_implicitFunctionOfProdDomain hinv] with t ht
    intro i
    have hi := congrFun ht i
    simpa [H, C, A, constraintMap, hv, u, z, add_assoc, sub_eq_zero] using hi

end EkelandVP.Constraints.EKFresh

-- Complete module: EKProof/FeasibleCurve.lean

open Filter
open scoped Topology

namespace EkelandVP.Constraints.EKFresh

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
theorem exists_feasible_curve {m : ℕ} (p : ℕ) (G : Fin m → V → ℝ)
    (hG : ∀ i, ContDiff ℝ 1 (G i)) (v : V) (hv : v ∈ feasibleSet p G)
    (hli : LinearIndependent ℝ (fun i : {i : Fin m // G i v = 0} => fderiv ℝ (G i) v))
    (h : V) (heq : ∀ i, i.val < p → fderiv ℝ (G i) v h = 0)
    (hineq : ∀ i, p ≤ i.val → G i v = 0 → 0 ≤ fderiv ℝ (G i) v h) :
    ∃ u : ℝ → V, u 0 = v ∧ HasDerivAt u h 0 ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ), u t ∈ feasibleSet p G := by
  classical
  let I := {i : Fin m // G i v = 0}
  obtain ⟨B,hB⟩ := constraintMap_rightInverse (fun i : I => fderiv ℝ (G i) v) hli
  obtain ⟨u,hu0,hu,hact⟩ := exists_corrected_curve (fun i : I => G i)
    (fun i => hG i) v h (fun i => i.property) B hB
  have hinact : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i : Fin m, G i v ≠ 0 → 0 ≤ G i (u t) := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : G i v = 0
    · exact Filter.Eventually.of_forall (by simp [hi])
    · have hip : p ≤ i.val := by
        by_contra hn
        exact hi ((hv i).1 (by omega))
      have hp : 0 < G i v := lt_of_le_of_ne ((hv i).2 hip) (Ne.symm hi)
      have hc := (hG i).continuous.continuousAt.comp hu.continuousAt
      have ht : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < G i (u t) := by
        apply hc.eventually (lt_mem_nhds _)
        simpa [hu0] using hp
      filter_upwards [ht] with t ht _ using ht.le
  refine ⟨u,hu0,hu,?_⟩
  filter_upwards [hact.filter_mono nhdsWithin_le_nhds,
    hinact.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hi ht0
  intro i
  constructor
  · intro hip
    have hiv := (hv i).1 hip
    simpa [heq i hip] using ht (⟨i,hiv⟩ : I)
  · intro hip
    by_cases hiv : G i v = 0
    · rw [ht (⟨i,hiv⟩ : I)]
      exact mul_nonneg (le_of_lt ht0) (hineq i hip hiv)
    · exact hi i hiv

omit [CompleteSpace V] in
theorem slope_bound_of_feasible_curve (F : V → ℝ) (v h : V)
    (hF : DifferentiableAt ℝ F v) (ε : ℝ)
    (u : ℝ → V) (hu0 : u 0 = v) (hu : HasDerivAt u h 0)
    (hs : ∀ᶠ t in 𝓝[>] (0 : ℝ), F v - ε * ‖u t - v‖ ≤ F (u t)) :
    -ε * ‖h‖ ≤ fderiv ℝ F v h := by
  have hf : HasDerivAt (fun t => F (u t)) (fderiv ℝ F v h) 0 := by
    have hd : HasFDerivAt F (fderiv ℝ F v) (u 0) := by simpa [hu0] using hF.hasFDerivAt
    exact hd.comp_hasDerivAt 0 hu
  apply le_of_tendsto_of_tendsto (hu.tendsto_slope_zero_right.norm.const_mul (-ε))
    hf.tendsto_slope_zero_right
  filter_upwards [hs, self_mem_nhdsWithin] with t ht ht0
  have htpos : 0 < t := ht0
  have hi := mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr htpos.le)
  simp only [zero_add, hu0, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos htpos, smul_eq_mul]
  nlinarith

end EkelandVP.Constraints.EKFresh

-- Complete module: EKProof/ConeEnvelope.lean

namespace EkelandVP.Constraints.EKFresh

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def coneEnvelope (K : Set V) (w : V →L[ℝ] ℝ) (ε : ℝ) (x : V) : ℝ :=
  sInf ((fun h => w h+ε*‖x-h‖) '' K)

theorem envelope_bdd (K : Set V) (w : V →L[ℝ] ℝ) (ε : ℝ) (hε : 0≤ε)
    (hw : ∀ h∈K, -ε*‖h‖≤w h) (x : V) :
    BddBelow ((fun h => w h+ε*‖x-h‖) '' K) := by
  refine ⟨-ε*‖x‖, ?_⟩
  rintro _ ⟨h,hK,rfl⟩
  have hn : ‖h‖≤‖x‖+‖x-h‖ := by
    have ht := norm_sub_le x (x-h)
    simpa only [sub_sub_cancel] using ht
  have hm := mul_le_mul_of_nonneg_left hn hε
  nlinarith [hw h hK]

theorem envelope_le (K : Set V) (w : V →L[ℝ] ℝ) (ε : ℝ) (hε : 0≤ε)
    (hw : ∀ h∈K, -ε*‖h‖≤w h) (x h : V) (hh : h∈K) :
    coneEnvelope K w ε x ≤ w h+ε*‖x-h‖ :=
  csInf_le (envelope_bdd K w ε hε hw x) ⟨h,hh,rfl⟩

theorem envelope_le_norm (K : Set V) (h0 : (0:V)∈K) (w : V →L[ℝ] ℝ)
    (ε : ℝ) (hε : 0≤ε) (hw : ∀ h∈K, -ε*‖h‖≤w h) (x : V) :
    coneEnvelope K w ε x ≤ ε*‖x‖ := by
  simpa using envelope_le K w ε hε hw x 0 h0

theorem envelope_zero (K : Set V) (h0 : (0:V)∈K) (w : V →L[ℝ] ℝ)
    (ε : ℝ) (hε : 0≤ε) (hw : ∀ h∈K, -ε*‖h‖≤w h) :
    coneEnvelope K w ε 0 = 0 := by
  apply le_antisymm
  · simpa using envelope_le_norm K h0 w ε hε hw 0
  · apply le_csInf (s := (fun h => w h+ε*‖0-h‖) '' K) ⟨_,0,h0,rfl⟩
    rintro _ ⟨h,hh,rfl⟩
    simp only [zero_sub, norm_neg]
    linarith [hw h hh]

theorem envelope_add (K : Set V) (h0 : (0:V)∈K)
    (hadd : ∀ x∈K, ∀ y∈K, x+y∈K) (w : V →L[ℝ] ℝ)
    (ε : ℝ) (hε : 0≤ε) (hw : ∀ h∈K, -ε*‖h‖≤w h) (x y : V) :
    coneEnvelope K w ε (x+y) ≤ coneEnvelope K w ε x+coneEnvelope K w ε y := by
  have hb (h : V) (hh : h∈K) :
      coneEnvelope K w ε (x+y)-(w h+ε*‖x-h‖) ≤ coneEnvelope K w ε y := by
    apply le_csInf (s := (fun h => w h+ε*‖y-h‖) '' K) ⟨_,0,h0,rfl⟩
    rintro _ ⟨k,hk,rfl⟩
    have hp := envelope_le K w ε hε hw (x+y) (h+k) (hadd h hh k hk)
    have hn : ‖x+y-(h+k)‖≤‖x-h‖+‖y-k‖ := by
      have he : x+y-(h+k) = (x-h)+(y-k) := by abel
      rw [he]
      exact norm_add_le _ _
    have hm := mul_le_mul_of_nonneg_left hn hε
    rw [map_add] at hp
    linarith
  have hc : coneEnvelope K w ε (x+y)-coneEnvelope K w ε y ≤ coneEnvelope K w ε x := by
    apply le_csInf (s := (fun h => w h+ε*‖x-h‖) '' K) ⟨_,0,h0,rfl⟩
    rintro _ ⟨h,hh,rfl⟩
    linarith [hb h hh]
  linarith

theorem envelope_smul_le (K : Set V) (h0 : (0:V)∈K)
    (hsmul : ∀ c:ℝ, 0<c → ∀ h∈K, c • h∈K) (w : V →L[ℝ] ℝ)
    (ε : ℝ) (hε : 0≤ε) (hw : ∀ h∈K, -ε*‖h‖≤w h)
    (c : ℝ) (hc : 0<c) (x : V) :
    coneEnvelope K w ε (c • x) ≤ c*coneEnvelope K w ε x := by
  have hp : coneEnvelope K w ε (c • x)/c ≤ coneEnvelope K w ε x := by
    apply le_csInf (s := (fun h => w h+ε*‖x-h‖) '' K) ⟨_,0,h0,rfl⟩
    rintro _ ⟨h,hh,rfl⟩
    apply (div_le_iff₀ hc).mpr
    have h := envelope_le K w ε hε hw (c • x) (c • h) (hsmul c hc h hh)
    simp only [map_smul, smul_eq_mul, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos hc] at h
    nlinarith
  exact (div_le_iff₀ hc).mp hp |>.trans_eq (mul_comm _ _)

theorem envelope_smul (K : Set V) (h0 : (0:V)∈K)
    (hsmul : ∀ c:ℝ, 0<c → ∀ h∈K, c • h∈K) (w : V →L[ℝ] ℝ)
    (ε : ℝ) (hε : 0≤ε) (hw : ∀ h∈K, -ε*‖h‖≤w h)
    (c : ℝ) (hc : 0<c) (x : V) :
    coneEnvelope K w ε (c • x) = c*coneEnvelope K w ε x := by
  apply le_antisymm (envelope_smul_le K h0 hsmul w ε hε hw c hc x)
  have h := envelope_smul_le K h0 hsmul w ε hε hw c⁻¹ (inv_pos.mpr hc) (c • x)
  simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul] at h
  have hm := mul_le_mul_of_nonneg_left h hc.le
  simpa [← mul_assoc, ne_of_gt hc] using hm

end EkelandVP.Constraints.EKFresh

-- Complete module: EKProof/ConeResidual.lean

namespace EkelandVP.Constraints.EKFresh

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem cone_residual (K : Set V) (h0 : (0:V)∈K)
    (hadd : ∀ x∈K, ∀ y∈K, x+y∈K)
    (hsmul : ∀ c:ℝ, 0<c → ∀ h∈K, c • h∈K)
    (w : V →L[ℝ] ℝ) (ε : ℝ) (hε : 0≤ε)
    (hw : ∀ h∈K, -ε*‖h‖≤w h) :
    ∃ f : V →L[ℝ] ℝ, ‖f‖≤ε ∧ ∀ h∈K, f h≤w h := by
  let f0 : V →ₗ.[ℝ] ℝ := (0 : V →ₗ[ℝ] ℝ).toPMap ⊥
  have hf0 : ∀ x : f0.domain, f0 x ≤ coneEnvelope K w ε x := by
    intro x
    have hx : (x:V)=0 := x.property
    change (0:ℝ) ≤ coneEnvelope K w ε (x:V)
    rw [hx, envelope_zero K h0 w ε hε hw]
  obtain ⟨f, _, hf⟩ := exists_extension_of_le_sublinear f0 (coneEnvelope K w ε)
    (fun c hc x => envelope_smul K h0 hsmul w ε hε hw c hc x)
    (envelope_add K h0 hadd w ε hε hw) hf0
  have hbound (x : V) : ‖f x‖≤ε*‖x‖ := by
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have h := (hf (-x)).trans (envelope_le_norm K h0 w ε hε hw (-x))
      simp only [map_neg, norm_neg] at h
      linarith
    · exact (hf x).trans (envelope_le_norm K h0 w ε hε hw x)
  refine ⟨f.mkContinuous ε hbound, f.mkContinuous_norm_le hε hbound, ?_⟩
  intro h hh
  have hp := (hf h).trans (envelope_le K w ε hε hw h h hh)
  simpa using hp

end EkelandVP.Constraints.EKFresh

-- Complete module: EKProof/FiniteMultipliers.lean

open scoped BigOperators

namespace EkelandVP.Constraints.EKFresh

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype I]

theorem finite_multipliers (a : I → V →L[ℝ] ℝ) (ha : LinearIndependent ℝ a)
    (E : I → Prop) (w : V →L[ℝ] ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hw : ∀ h, (∀ i, E i → a i h = 0) → (∀ i, ¬ E i → 0 ≤ a i h) →
      -ε * ‖h‖ ≤ w h) :
    ∃ c : I → ℝ, (∀ i, ¬ E i → 0 ≤ c i) ∧ ‖w - ∑ i, c i • a i‖ ≤ ε := by
  classical
  let K : Set V := {h | (∀ i, E i → a i h = 0) ∧ (∀ i, ¬ E i → 0 ≤ a i h)}
  have h0 : (0 : V) ∈ K := by simp [K]
  have hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K := by
    intro x hx y hy
    exact ⟨fun i hi => by simp [map_add, hx.1 i hi, hy.1 i hi],
      fun i hi => by simpa only [map_add] using add_nonneg (hx.2 i hi) (hy.2 i hi)⟩
  have hsmul : ∀ c : ℝ, 0 < c → ∀ x ∈ K, c • x ∈ K := by
    intro c hc x hx
    exact ⟨fun i hi => by simp [map_smul, hx.1 i hi],
      fun i hi => by simpa only [map_smul, smul_eq_mul] using mul_nonneg hc.le (hx.2 i hi)⟩
  obtain ⟨f,hfn,hfw⟩ := cone_residual K h0 hadd hsmul w ε hε
    (fun h hh => hw h hh.1 hh.2)
  let ell := w - f
  have hell : ∀ x ∈ K, 0 ≤ ell x := by
    intro x hx
    exact sub_nonneg.mpr (hfw x hx)
  have hker : ∀ x, constraintMap a x = 0 → ell x = 0 := by
    intro x hx
    have hz : ∀ i, a i x = 0 := fun i => congrFun hx i
    have hkx : x ∈ K := by simp [K, hz]
    have hkn : -x ∈ K := by simp [K, hz]
    have hp := hell x hkx
    have hn := hell (-x) hkn
    have hn' : ell x ≤ 0 := by simpa only [map_neg, neg_nonneg] using hn
    exact le_antisymm hn' hp
  obtain ⟨B,hB⟩ := constraintMap_rightInverse a ha
  have hfct := finite_constraint_factor a B hB ell hker
  refine ⟨fun i => ell (B (Pi.single i 1)), ?_, ?_⟩
  · intro i hi
    apply hell
    have htest : ∀ j, a j (B (Pi.single i 1)) = (Pi.single i 1 : I → ℝ) j :=
      fun j => congrFun (hB (Pi.single i 1)) j
    constructor
    · intro j hj
      have hji : j ≠ i := by intro he; subst j; exact hi hj
      simp [htest, hji]
    · intro j _
      rw [htest]
      by_cases hji : j = i <;> simp [hji]
  · rw [← hfct]
    simpa [ell] using hfn

end EkelandVP.Constraints.EKFresh

-- Complete module: EKProof/DescentSets.lean

namespace EkelandVP.Constraints.EKFresh

variable {E : Type*} [MetricSpace E]

def Descent (F : E → ℝ) (ε : ℝ) (x y : E) : Prop := F y+ε*dist y x≤F x

theorem descent_refl (F : E → ℝ) (ε : ℝ) (x : E) : Descent F ε x x := by
  simp [Descent]

theorem descent_trans (F : E → ℝ) (ε : ℝ) (hε : 0≤ε) {x y z : E}
    (hxy : Descent F ε x y) (hyz : Descent F ε y z) : Descent F ε x z := by
  have hd := mul_le_mul_of_nonneg_left (dist_triangle z y x) hε
  dsimp [Descent] at *
  linarith

theorem descent_value_le (F : E → ℝ) (ε : ℝ) (hε : 0≤ε) {x y : E}
    (h : Descent F ε x y) : F y≤F x := by
  have hp := mul_nonneg hε (dist_nonneg (x := y) (y := x))
  dsimp [Descent] at h
  linarith

omit [MetricSpace E] in
theorem exists_near_inf (F : E → ℝ) (S : Set E) (hne : S.Nonempty)
    (hb : BddBelow (F '' S)) (δ : ℝ) (hδ : 0<δ) :
    ∃ x∈S, ∀ y∈S, F x≤F y+δ := by
  obtain ⟨z,⟨x,hx,rfl⟩,hz⟩ := exists_lt_of_csInf_lt (hne.image F)
    (show sInf (F '' S)<sInf (F '' S)+δ by linarith)
  refine ⟨x,hx,?_⟩
  intro y hy
  have hi := csInf_le hb (Set.mem_image_of_mem F hy)
  linarith

theorem descent_near (F : E → ℝ) (ε : ℝ) (hb : BddBelow (Set.range F))
    (x : E) (δ : ℝ) (hδ : 0<δ) :
    ∃ y, Descent F ε x y ∧ ∀ z, Descent F ε x z → F y≤F z+δ := by
  apply exists_near_inf F {y | Descent F ε x y} ⟨x,descent_refl F ε x⟩
    (hb.mono (by rintro _ ⟨y,_,rfl⟩; exact ⟨y,rfl⟩)) δ hδ

theorem exists_descent_sequence (F : E → ℝ) (ε : ℝ)
    (hb : BddBelow (Set.range F)) (x0 : E) :
    ∃ x : ℕ → E, x 0=x0 ∧ ∀ n,
      Descent F ε (x n) (x (n+1)) ∧
        ∀ z, Descent F ε (x n) z → F (x (n+1))≤F z+(1/2:ℝ)^n := by
  classical
  have h (n : ℕ) (x : E) := descent_near F ε hb x ((1/2:ℝ)^n) (by positivity)
  choose next hn using h
  let x : ℕ → E := fun n => Nat.rec x0 (fun n y => next n y) n
  refine ⟨x,rfl,?_⟩
  intro n
  exact hn n (x n)

end EkelandVP.Constraints.EKFresh

-- Complete module: EKProof/DescentLimit.lean

namespace EkelandVP.Constraints.EKFresh
open Filter Topology

variable {E : Type*} [MetricSpace E] [CompleteSpace E]

theorem descent_sequence_limit (F : E → ℝ) (hF : Continuous F)
    (ε : ℝ) (hε : 0 < ε) (hb : BddBelow (Set.range F))
    (x : ℕ → E) (hs : ∀ n, Descent F ε (x n) (x (n+1))) :
    ∃ v, Tendsto x atTop (𝓝 v) ∧ ∀ n, Descent F ε (x n) v := by
  have hnm (n m : ℕ) (hnm : n ≤ m) : Descent F ε (x n) (x m) := by
    induction m, hnm using Nat.le_induction with
    | base => exact descent_refl F ε _
    | succ m _ ih => exact descent_trans F ε hε.le ih (hs m)
  have ha : Antitone (fun n => F (x n)) := fun n m h => descent_value_le F ε hε.le (hnm n m h)
  have hb' : BddBelow (Set.range (fun n => F (x n))) := hb.mono (by
    rintro _ ⟨n,rfl⟩
    exact ⟨x n,rfl⟩)
  let l := sInf (Set.range (fun n => F (x n)))
  have hl : Tendsto (fun n => F (x n)) atTop (𝓝 l) := tendsto_atTop_ciInf ha hb'
  have hlo (n : ℕ) : l ≤ F (x n) := csInf_le hb' ⟨n,rfl⟩
  have hzero : Tendsto (fun n => (F (x n)-l)/ε) atTop (𝓝 0) := by
    simpa using (hl.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => l) atTop (𝓝 l))).div_const ε
  have hca : CauchySeq x := cauchySeq_of_le_tendsto_0' (fun n => (F (x n)-l)/ε) (by
    intro n m h
    apply (le_div_iff₀ hε).mpr
    have hd := hnm n m h
    dsimp [Descent] at hd
    rw [dist_comm] at hd
    nlinarith [hlo m]) hzero
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hca
  refine ⟨v,hv,?_⟩
  intro n
  have hd : Tendsto (fun m => F (x m)+ε*dist (x m) (x n)) atTop
      (𝓝 (F v+ε*dist v (x n))) :=
    ((hF.tendsto v).comp hv).add
      ((hv.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => x n) atTop (𝓝 (x n)))).const_mul ε)
  exact le_of_tendsto hd (Filter.eventually_atTop.2 ⟨n,fun m hm => hnm n m hm⟩)

theorem variational_above (F : E → ℝ) (hF : Continuous F)
    (ε : ℝ) (hε : 0 < ε) (hb : BddBelow (Set.range F)) (x0 : E) :
    ∃ v, F v ≤ F x0 ∧ ∀ y, F v ≤ F y+ε*dist y v := by
  obtain ⟨x,hx,hs⟩ := exists_descent_sequence F ε hb x0
  obtain ⟨v,hv,hd⟩ := descent_sequence_limit F hF ε hε hb x (fun n => (hs n).1)
  refine ⟨v,?_,?_⟩
  · have h := descent_value_le F ε hε.le (hd 0)
    simpa only [hx] using h
  · intro y
    by_cases hy : Descent F ε v y
    · have hlow (n : ℕ) : F v ≤ F y+(1/2:ℝ)^n := by
        have h1 := descent_value_le F ε hε.le (hd (n+1))
        have h2 := (hs n).2 y (descent_trans F ε hε.le (hd n) hy)
        linarith
      have hp : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have hle : F v ≤ F y := by
        simpa using ge_of_tendsto (tendsto_const_nhds.add hp) (Filter.Eventually.of_forall hlow)
      dsimp [Descent] at hy
      have hdist : dist y v=0 := by nlinarith [dist_nonneg (x := y) (y := v)]
      have he : y=v := dist_eq_zero.mp hdist
      simp [he]
    · dsimp [Descent] at hy
      linarith

end EkelandVP.Constraints.EKFresh

-- Complete module: EKProof/ClosedVariational.lean

namespace EkelandVP.Constraints.EKFresh

variable {E : Type*} [MetricSpace E] [CompleteSpace E]

theorem closed_variational (C : Set E) (hC : IsClosed C) (hne : C.Nonempty)
    (F : E → ℝ) (hF : Continuous F) (hb : BddBelow (F '' C))
    (ε : ℝ) (hε : 0<ε) :
    ∃ v∈C, (∀ w∈C, F v≤F w+ε^2) ∧ ∀ w∈C, F v≤F w+ε*dist w v := by
  let : CompleteSpace C := hC.isComplete.completeSpace_coe
  obtain ⟨x0,hx0,hnear⟩ := exists_near_inf F C hne hb (ε^2) (sq_pos_of_pos hε)
  let Fc : C → ℝ := fun x => F x
  have hc : Continuous Fc := hF.comp continuous_subtype_val
  have hb' : BddBelow (Set.range Fc) := hb.mono (by
    rintro _ ⟨x,rfl⟩
    exact ⟨x,x.property,rfl⟩)
  obtain ⟨v,hval,hslope⟩ := variational_above Fc hc ε hε hb' ⟨x0,hx0⟩
  refine ⟨v,v.property,?_,?_⟩
  · intro w hw
    exact hval.trans (hnear w hw)
  · intro w hw
    exact hslope ⟨w,hw⟩

end EkelandVP.Constraints.EKFresh

-- Complete module: EKProof/NativeConclusion.lean

namespace EkelandVP.Constraints.EKFresh

theorem native_theorem_3_1 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {m : ℕ} (p : ℕ) (hp : p ≤ m) (F : V → ℝ) (G : Fin m → V → ℝ)
    (hF : Differentiable ℝ F) (hG : ∀ i, ContDiff ℝ 1 (G i))
    (hreg : IsRegular p G)
    (hne : (feasibleSet p G).Nonempty) (hbdd : BddBelow (F '' feasibleSet p G))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ v ∈ feasibleSet p G,
      (∀ w ∈ feasibleSet p G, F v ≤ F w + ε ^ 2) ∧
      ∃ lam : Fin m → ℝ,
        (∀ i : Fin m, p ≤ i.val → 0 ≤ lam i) ∧
        (∀ i : Fin m, G i v ≠ 0 → lam i = 0) ∧
        ‖fderiv ℝ F v - ∑ i, lam i • fderiv ℝ (G i) v‖ ≤ ε := by
  classical
  have _ := hp
  have hC : IsClosed (feasibleSet p G) := by
    simp only [feasibleSet, Set.ofPred_forall, Set.ofPred_and]
    apply isClosed_iInter
    intro i
    exact (isClosed_iInter fun _ => isClosed_eq (hG i).continuous continuous_const).inter
      (isClosed_iInter fun _ => isClosed_le continuous_const (hG i).continuous)
  obtain ⟨v,hv,hnear,hslope⟩ := closed_variational (feasibleSet p G) hC hne F
    hF.continuous hbdd ε hε
  let I := {i : Fin m // G i v = 0}
  let a : I → V →L[ℝ] ℝ := fun i => fderiv ℝ (G i) v
  have hcone : ∀ h, (∀ i : I, i.val.val < p → a i h = 0) →
      (∀ i : I, ¬i.val.val < p → 0 ≤ a i h) → -ε * ‖h‖ ≤ fderiv ℝ F v h := by
    intro h heq hineq
    obtain ⟨u,hu0,hu,hufeas⟩ := exists_feasible_curve p G hG v hv (hreg v hv) h
      (fun i hi => heq ⟨i,(hv i).1 hi⟩ hi)
      (fun i hi hz => hineq ⟨i,hz⟩ (by change ¬i.val < p; omega))
    apply slope_bound_of_feasible_curve F v h (hF v) ε u hu0 hu
    filter_upwards [hufeas] with t ht
    have hh := hslope (u t) ht
    rw [dist_eq_norm] at hh
    linarith
  obtain ⟨c,hc,hnorm⟩ := finite_multipliers a (hreg v hv)
    (fun i : I => i.val.val < p) (fderiv ℝ F v) ε hε.le hcone
  let lam : Fin m → ℝ := fun i => if hi : G i v = 0 then c ⟨i,hi⟩ else 0
  have hsum : (∑ i, lam i • fderiv ℝ (G i) v) = ∑ i : I, c i • a i := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin m => G i v = 0)]
    have h1 : (∑ i : I, lam i • fderiv ℝ (G i) v) = ∑ i : I, c i • a i := by
      apply Finset.sum_congr rfl
      intro i _
      simp [lam, i.property, a]
    have h2 : (∑ i : {i : Fin m // ¬G i v = 0}, lam i • fderiv ℝ (G i) v) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp [lam, i.property]
    rw [h1, h2, add_zero]
  refine ⟨v,hv,hnear,lam,?_,?_,?_⟩
  · intro i hi
    dsimp [lam]
    split_ifs with hz
    · exact hc ⟨i,hz⟩ (by change ¬i.val < p; omega)
    · exact le_rfl
  · intro i hi
    simp [lam, hi]
  · rw [hsum]
    exact hnorm

end EkelandVP.Constraints.EKFresh

-- Complete module: EKProof/FinalRoot.lean

namespace EkelandVP.Constraints

/-- Ekeland (1974), Theorem 3.1, p. 330: on a Banach space `V`, let `F` be Fréchet-differentiable and
`G_1, …, G_m` be `C¹` with the regularity assumption (3.4), and let `F` be bounded below on the
(nonempty) feasible set `𝒞` (3.5). Then for every `ε > 0` there is `v_ε ∈ 𝒞` with
`F(v_ε) ≤ inf_𝒞 F + ε²` (3.6), and reals `λ_1, …, λ_m` with `λ_i ≥ 0` for the inequality constraints,
`λ_i = 0` when `G_i(v_ε) ≠ 0`, and `‖F'(v_ε) - Σ λ_i G_i'(v_ε)‖* ≤ ε` (3.7). -/
theorem theorem_3_1 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {m : ℕ} (p : ℕ) (hp : p ≤ m) (F : V → ℝ) (G : Fin m → V → ℝ)
    (hF : Differentiable ℝ F) (hG : ∀ i, ContDiff ℝ 1 (G i))
    (hreg : IsRegular p G)
    (hne : (feasibleSet p G).Nonempty) (hbdd : BddBelow (F '' feasibleSet p G))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ v ∈ feasibleSet p G,
      (∀ w ∈ feasibleSet p G, F v ≤ F w + ε ^ 2) ∧
      ∃ lam : Fin m → ℝ,
        (∀ i : Fin m, p ≤ i.val → 0 ≤ lam i) ∧
        (∀ i : Fin m, G i v ≠ 0 → lam i = 0) ∧
        ‖fderiv ℝ F v - ∑ i, lam i • fderiv ℝ (G i) v‖ ≤ ε := by
  exact EKFresh.native_theorem_3_1 p hp F G hF hG hreg hne hbdd ε hε

end EkelandVP.Constraints


open EkelandVP.Constraints
theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {m : ℕ} (p : ℕ) (hp : p ≤ m) (F : V → ℝ) (G : Fin m → V → ℝ)
    (hF : Differentiable ℝ F) (hG : ∀ i, ContDiff ℝ 1 (G i))
    (hreg : IsRegular p G)
    (hne : (feasibleSet p G).Nonempty) (hbdd : BddBelow (F '' feasibleSet p G))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ v ∈ feasibleSet p G,
      (∀ w ∈ feasibleSet p G, F v ≤ F w + ε ^ 2) ∧
      ∃ lam : Fin m → ℝ,
        (∀ i : Fin m, p ≤ i.val → 0 ≤ lam i) ∧
        (∀ i : Fin m, G i v ≠ 0 → lam i = 0) ∧
        ‖fderiv ℝ F v - ∑ i, lam i • fderiv ℝ (G i) v‖ ≤ ε := by
  exact EkelandVP.Constraints.theorem_3_1 p hp F G hF hG hreg hne hbdd ε hε
