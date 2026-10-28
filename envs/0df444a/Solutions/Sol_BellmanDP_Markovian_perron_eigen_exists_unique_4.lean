-- Prove2me | solution 4 for BellmanDP.Markovian.perron_eigen_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:31:17.160261+00:00
-- url     : https://prove2.me/submissions/28155924-669b-4d99-bdfe-646090336ed5

import Mathlib
import Definitions.Def_BellmanDP_Markovian_Discrete
import Theorems.Thm_Brouwer_exists_fixedPoint_closedBall_contDiff

-- carved verbatim out of submission 9c73e111-00c3-46d9-95b1-8aaa15e78ec5, lines 1065-1073

section
open BellmanDP
open BellmanDP.Markovian
open Metric Set MeasureTheory

theorem L3_brouwer_ball_scalar_approx {d : ℕ} (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : ContinuousOn φ (closedBall 0 1)) (η : ℝ) (hη : 0 < η) :
    ∃ G : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 G ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, |G x - φ x| < η := by
  set B : Set (EuclideanSpace ℝ (Fin d)) := closedBall 0 1 with hB
  have : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  let A : Subalgebra ℝ C(B, ℝ) :=
    { carrier := {g | ∃ G : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 G ∧ ∀ x : B, g x = G x}
      mul_mem' := by
        rintro a b ⟨Ga, hGa, ha⟩ ⟨Gb, hGb, hb⟩
        exact ⟨fun x => Ga x * Gb x, hGa.mul hGb, fun x => by simp [ha, hb]⟩
      add_mem' := by
        rintro a b ⟨Ga, hGa, ha⟩ ⟨Gb, hGb, hb⟩
        exact ⟨fun x => Ga x + Gb x, hGa.add hGb, fun x => by simp [ha, hb]⟩
      algebraMap_mem' := fun r => ⟨fun _ => r, contDiff_const, fun x => by simp⟩ }
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    have : ∃ i, (x : EuclideanSpace ℝ (Fin d)) i ≠ (y : EuclideanSpace ℝ (Fin d)) i := by
      by_contra h
      push Not at h
      apply hxy
      apply Subtype.ext
      ext i
      exact h i
    obtain ⟨i, hi⟩ := this
    refine ⟨fun z : B => (z : EuclideanSpace ℝ (Fin d)) i, ?_, hi⟩
    refine ⟨⟨fun z : B => (z : EuclideanSpace ℝ (Fin d)) i, by fun_prop⟩, ?_, rfl⟩
    exact ⟨fun z => z i, (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff,
      fun z => rfl⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints A hsep
    (fun x : B => φ x) hφ.domRestrict η hη
  obtain ⟨G, hG, hgG⟩ := g.2
  refine ⟨G, hG, fun x hx => ?_⟩
  have := hg ⟨x, hx⟩
  rw [Real.norm_eq_abs] at this
  simpa [hgG] using this

theorem L3_brouwer_ball_vec_approx {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ContinuousOn f (closedBall 0 1)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), ContDiff ℝ 1 G ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖G x - f x‖ < δ := by
  set η : ℝ := δ / (d + 1) with hη_def
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  have hη : 0 < η := div_pos hδ hd1
  have hcoord : ∀ i : Fin d, ∃ Gi : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 Gi ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, |Gi x - f x i| < η := by
    intro i
    refine L3_brouwer_ball_scalar_approx (fun x => f x i) ?_ η hη
    exact (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous.comp_continuousOn hf
  choose Gi hGi hGiapprox using hcoord
  refine ⟨fun x => (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => Gi i x), ?_, ?_⟩
  · exact (EuclideanSpace.equiv (Fin d) ℝ).symm.contDiff.comp (contDiff_pi.2 fun i => hGi i)
  · intro x hx
    set v := (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => Gi i x) - f x with hv
    have hvi : ∀ i, v i = Gi i x - f x i := by
      intro i
      simp [hv]
    have hsq : ‖v‖ ^ 2 ≤ d * η ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc ∑ i, (v i) ^ 2 ≤ ∑ _i : Fin d, η ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            rw [hvi i]
            have := hGiapprox i x hx
            rw [← sq_abs]
            have h0 : 0 ≤ |Gi i x - f x i| := abs_nonneg _
            nlinarith
        _ = d * η ^ 2 := by simp
    have hlt : ‖v‖ ^ 2 < δ ^ 2 := by
      have hδη : δ = (d + 1) * η := by rw [hη_def]; field_simp
      rw [hδη]
      have : (d : ℝ) * η ^ 2 < ((d : ℝ) + 1) ^ 2 * η ^ 2 := by
        have hdd : (d : ℝ) < ((d : ℝ) + 1) ^ 2 := by nlinarith
        have := pow_pos hη 2
        nlinarith
      nlinarith
    have hn : 0 ≤ ‖v‖ := norm_nonneg _
    nlinarith

theorem L3_brouwer_ball {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ContinuousOn f (closedBall 0 1)) (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, f x = x := by
  by_contra hno
  push Not at hno
  -- Step 1: minimal displacement
  have hcpt : IsCompact (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := isCompact_closedBall 0 1
  have hne : (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).Nonempty :=
    ⟨0, mem_closedBall_self zero_le_one⟩
  have hcont : ContinuousOn (fun x => ‖f x - x‖) (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    (hf.sub continuousOn_id).norm
  obtain ⟨x₀, hx₀, hmin⟩ := hcpt.exists_isMinOn hne hcont
  set ε : ℝ := ‖f x₀ - x₀‖ with hε_def
  have hε : 0 < ε := norm_pos_iff.2 (sub_ne_zero.2 (hno x₀ hx₀))
  have hεle : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ε ≤ ‖f x - x‖ :=
    fun x hx => hmin hx
  -- Step 2: smooth approximation
  set η : ℝ := ε / 2 with hη_def
  have hη : 0 < η := half_pos hε
  obtain ⟨G, hG, hGapprox⟩ := L3_brouwer_ball_vec_approx f hf η hη
  -- Step 3: rescale
  set c : ℝ := 1 + η with hc_def
  have hc : 0 < c := by positivity
  set g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => c⁻¹ • G x with hg_def
  have hgC1 : ContDiff ℝ 1 g := hG.const_smul c⁻¹
  have hGnorm : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖G x‖ ≤ c := by
    intro x hx
    have h1 : ‖f x‖ ≤ 1 := by simpa using hmaps hx
    have h2 := hGapprox x hx
    calc ‖G x‖ = ‖(G x - f x) + f x‖ := by rw [sub_add_cancel]
      _ ≤ ‖G x - f x‖ + ‖f x‖ := norm_add_le _ _
      _ ≤ c := by rw [hc_def]; linarith
  have hgmaps : MapsTo g (closedBall 0 1) (closedBall 0 1) := by
    intro x hx
    rw [mem_closedBall_zero_iff, hg_def]
    simp only
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc)]
    calc c⁻¹ * ‖G x‖ ≤ c⁻¹ * c := by
          exact mul_le_mul_of_nonneg_left (hGnorm x hx) (inv_pos.2 hc).le
      _ = 1 := inv_mul_cancel₀ hc.ne'
  have hgf : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖g x - f x‖ < ε := by
    intro x hx
    have h1 : ‖f x‖ ≤ 1 := by simpa using hmaps hx
    have h2 := hGapprox x hx
    have hkey : c • (g x - f x) = (G x - f x) - η • f x := by
      rw [hg_def]
      simp only
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hc.ne', one_smul, hc_def, add_smul, one_smul]
      abel
    have hnorm : c * ‖g x - f x‖ ≤ ‖G x - f x‖ + η * ‖f x‖ := by
      have := congrArg norm hkey
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc] at this
      rw [this]
      calc ‖(G x - f x) - η • f x‖ ≤ ‖G x - f x‖ + ‖η • f x‖ := norm_sub_le _ _
        _ = ‖G x - f x‖ + η * ‖f x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    have hc1 : 1 ≤ c := by rw [hc_def]; linarith
    have hn0 : 0 ≤ ‖g x - f x‖ := norm_nonneg _
    have : η * ‖f x‖ ≤ η := by nlinarith
    nlinarith
  obtain ⟨x, hx, hfix⟩ := Brouwer.exists_fixedPoint_closedBall_contDiff g hgC1 hgmaps
  have h1 := hεle x hx
  have h2 := hgf x hx
  rw [hfix, norm_sub_rev] at h2
  linarith

theorem L4_retraction {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {K : Set F} (hne : K.Nonempty) (hc : IsComplete K) (hconv : Convex ℝ K) :
    ∃ p : F → F, Continuous p ∧ (∀ x, p x ∈ K) ∧ (∀ x ∈ K, p x = x) := by
  choose p hpK hpeq using exists_norm_eq_iInf_of_complete_convex hne hc hconv
  have hin : ∀ x, ∀ w ∈ K, inner ℝ (x - p x) (w - p x) ≤ 0 := fun x =>
    (norm_eq_iInf_iff_real_inner_le_zero hconv (hpK x)).1 (hpeq x)
  refine ⟨p, ?_, hpK, ?_⟩
  · have hlip : LipschitzWith 1 p := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      simp only [NNReal.coe_one, one_mul, dist_eq_norm]
      have h1 := hin x (p y) (hpK y)
      have h2 := hin y (p x) (hpK x)
      have key : ‖p x - p y‖ ^ 2 ≤ inner ℝ (x - y) (p x - p y) := by
        have e : inner ℝ (x - y) (p x - p y) - ‖p x - p y‖ ^ 2 =
            -inner ℝ (x - p x) (p y - p x) - inner ℝ (y - p y) (p x - p y) := by
          rw [← real_inner_self_eq_norm_sq]
          simp only [inner_sub_left, inner_sub_right, real_inner_comm]
          ring
        linarith
      have hcs := real_inner_le_norm (x - y) (p x - p y)
      rcases eq_or_lt_of_le (norm_nonneg (p x - p y)) with h | h
      · rw [← h]; exact norm_nonneg _
      · nlinarith
    exact hlip.continuous
  · intro x hx
    have h0 : ‖x - p x‖ ^ 2 ≤ 0 := by
      rw [← real_inner_self_eq_norm_sq]; exact hin x x hx
    have h1 : ‖x - p x‖ = 0 := by nlinarith [norm_nonneg (x - p x)]
    exact (norm_sub_eq_zero_iff.1 h1).symm

theorem L4_brouwer_euclid {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hKconv : Convex ℝ K)
    (hKcpt : IsCompact K) (hKne : K.Nonempty)
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hf : ContinuousOn f K)
    (hfK : MapsTo f K K) : ∃ x ∈ K, f x = x := by
  obtain ⟨p, hpc, hpK, hpid⟩ := L4_retraction hKne hKcpt.isComplete hKconv
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hKcpt.isBounded
  set R : ℝ := max R₀ 1 with hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKR : K ⊆ closedBall 0 R := hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  let g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun z => R⁻¹ • f (p (R • z))
  have hgc : ContinuousOn g (closedBall 0 1) := by
    have hc : ContinuousOn (fun z => f (p (R • z))) univ :=
      hf.comp (hpc.comp (continuous_const_smul R)).continuousOn (fun z _ => hpK _)
    exact (hc.mono (subset_univ _)).const_smul R⁻¹
  have hgm : MapsTo g (closedBall 0 1) (closedBall 0 1) := by
    intro z _
    have h1 := hKR (hfK (hpK (R • z)))
    rw [mem_closedBall_zero_iff] at h1 ⊢
    simp only [g, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hRpos]
    rw [inv_mul_le_iff₀ hRpos]
    linarith
  obtain ⟨z, -, hz⟩ := L3_brouwer_ball g hgc hgm
  have hx : f (p (R • z)) = R • z := by
    have := congrArg (fun v => R • v) hz
    simpa [g, smul_smul, mul_inv_cancel₀ hRpos.ne'] using this
  have hxK : R • z ∈ K := hx ▸ hfK (hpK _)
  refine ⟨R • z, hxK, ?_⟩
  rw [hpid _ hxK] at hx
  exact hx

theorem brouwer_local_fp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K : Set E}
    (hKconv : Convex ℝ K) (hKcpt : IsCompact K) (hKne : K.Nonempty)
    (f : E → E) (hf : ContinuousOn f K) (hfK : Set.MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  classical
  let φ : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  have hconv' : Convex ℝ (φ '' K) :=
    hKconv.linear_image (φ : E →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
  have hcont : ContinuousOn (φ ∘ f ∘ φ.symm) (φ '' K) := by
    refine φ.continuous.comp_continuousOn (hf.comp φ.symm.continuous.continuousOn ?_)
    rintro _ ⟨y, hy, rfl⟩
    simpa using hy
  have hmaps : MapsTo (φ ∘ f ∘ φ.symm) (φ '' K) (φ '' K) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨f y, hfK hy, by simp⟩
  obtain ⟨x, ⟨y, hyK, rfl⟩, hx⟩ :=
    L4_brouwer_euclid hconv' (hKcpt.image φ.continuous) (hKne.image φ) _ hcont hmaps
  refine ⟨y, hyK, ?_⟩
  apply φ.injective
  simpa using hx

end

section
open BellmanDP
open BellmanDP.Markovian
open Metric Set MeasureTheory
open Finset Matrix

lemma pe_nn (k : ℂ) : ((‖k‖₊ : NNReal) : ENNReal) = ENNReal.ofReal ‖k‖ := by
  rw [ENNReal.ofReal, norm_toNNReal]

lemma pe_mem_spec_iff {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (k : ℂ) :
    k ∈ spectrum ℂ M ↔ ∃ v : Fin N → ℂ, v ≠ 0 ∧ M *ᵥ v = k • v := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero] at h
    exact h.symm
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec, h, sub_self]

lemma pe_mulVec_apply {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℂ) (i : Fin N) :
    (A.map (algebraMap ℝ ℂ) *ᵥ v) i = ∑ j, ((A i j : ℝ) : ℂ) * v j := by
  simp [Matrix.mulVec, dotProduct, Matrix.map_apply]

lemma pe_spec_upper {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (y : Fin N → ℝ) (hy : ∀ i, 0 < y i) (lam : ℝ) (hl : 0 ≤ lam)
    (hAy : ∀ i, ∑ j, A i j * y j ≤ lam * y i) :
    spectralRadius ℂ (A.map (algebraMap ℝ ℂ)) ≤ ENNReal.ofReal lam := by
  refine iSup₂_le fun k hk => ?_
  obtain ⟨v, hv0, hv⟩ := (pe_mem_spec_iff _ k).1 hk
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
    exact ⟨j, Finset.mem_univ _⟩
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun j => ‖v j‖ / y j) hne
  set t := ‖v i0‖ / y i0 with ht
  have hle : ∀ j, ‖v j‖ ≤ t * y j := by
    intro j
    have := hi0 j (Finset.mem_univ _)
    rw [div_le_iff₀ (hy j)] at this
    exact this
  have htpos : 0 < t := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
    have h1 : 0 < ‖v j‖ := norm_pos_iff.2 hj
    have := hle j
    by_contra hc
    push_neg at hc
    nlinarith [hy j]
  have hvi0 : ‖v i0‖ = t * y i0 := by
    rw [ht, div_mul_cancel₀ _ (hy i0).ne']
  have key : ‖k‖ * ‖v i0‖ ≤ lam * ‖v i0‖ := by
    have e : k * v i0 = ∑ j, ((A i0 j : ℝ) : ℂ) * v j := by
      have := congrFun hv i0
      rw [pe_mulVec_apply] at this
      rw [this]; simp
    calc ‖k‖ * ‖v i0‖ = ‖k * v i0‖ := (norm_mul _ _).symm
      _ = ‖∑ j, ((A i0 j : ℝ) : ℂ) * v j‖ := by rw [e]
      _ ≤ ∑ j, ‖((A i0 j : ℝ) : ℂ) * v j‖ := norm_sum_le _ _
      _ = ∑ j, A i0 j * ‖v j‖ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hA i0 j)]
      _ ≤ ∑ j, A i0 j * (t * y j) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hle j) (hA i0 j)
      _ = t * ∑ j, A i0 j * y j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
      _ ≤ t * (lam * y i0) := mul_le_mul_of_nonneg_left (hAy i0) htpos.le
      _ = lam * ‖v i0‖ := by rw [hvi0]; ring
  have hpos : 0 < ‖v i0‖ := by rw [hvi0]; exact mul_pos htpos (hy i0)
  have hk : ‖k‖ ≤ lam := le_of_mul_le_mul_right key hpos
  rw [pe_nn]
  exact ENNReal.ofReal_le_ofReal hk

lemma pe_spec_lower {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (y : Fin N → ℝ) (hy0 : y ≠ 0) (lam : ℝ) (hl : 0 ≤ lam)
    (hAy : ∀ i, ∑ j, A i j * y j = lam * y i) :
    ENNReal.ofReal lam ≤ spectralRadius ℂ (A.map (algebraMap ℝ ℂ)) := by
  have hmem : ((lam : ℝ) : ℂ) ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) := by
    rw [pe_mem_spec_iff]
    refine ⟨fun j => ((y j : ℝ) : ℂ), ?_, ?_⟩
    · intro h
      apply hy0
      funext j
      have := congrFun h j
      simpa using this
    · funext i
      rw [pe_mulVec_apply]
      have := hAy i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← Complex.ofReal_mul, ← this]
      push_cast
      rfl
  have := le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ))) =>
    (‖k‖₊ : ENNReal)) _ hmem
  refine le_trans ?_ this
  rw [pe_nn]
  apply ENNReal.ofReal_le_ofReal
  rw [Complex.norm_real, Real.norm_of_nonneg hl]

lemma pe_cmp {N : ℕ} (hN : 0 < N) {Q : Fin N → Type*}
    (a : (i : Fin N) → Q i → Fin N → ℝ) (S : (i : Fin N) → Set (Q i))
    (hpos : ∀ (i : Fin N), ∀ q ∈ S i, ∀ j : Fin N, 0 < a i q j)
    (lam mu : ℝ) (y z : Fin N → ℝ) (hy : ∀ i, 0 < y i) (hz : ∀ i, 0 < z i)
    (hY : IsMaxEigenpair a S lam y) (hZ : IsMaxEigenpair a S mu z) :
    ∃ t : ℝ, 0 < t ∧ (∀ j, y j ≤ t * z j) ∧ lam ≤ mu ∧ (lam = mu → y = t • z) := by
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun j => y j / z j) hne
  set t := y i0 / z i0 with ht
  have hle : ∀ j, y j ≤ t * z j := by
    intro j
    have := hi0 j (Finset.mem_univ _)
    rw [div_le_iff₀ (hz j)] at this
    exact this
  have htpos : 0 < t := div_pos (hy i0) (hz i0)
  have hyi0 : y i0 = t * z i0 := by rw [ht, div_mul_cancel₀ _ (hz i0).ne']
  obtain ⟨⟨q, hq, hqe⟩, -⟩ := hY i0
  simp only at hqe
  have hzub : ∑ j, a i0 q j * z j ≤ mu * z i0 := (hZ i0).2 ⟨q, hq, rfl⟩
  have hlam : lam * y i0 ≤ mu * y i0 := by
    calc lam * y i0 = ∑ j, a i0 q j * y j := hqe.symm
      _ ≤ ∑ j, a i0 q j * (t * z j) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hle j) (hpos i0 q hq j).le
      _ = t * ∑ j, a i0 q j * z j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
      _ ≤ t * (mu * z i0) := mul_le_mul_of_nonneg_left hzub htpos.le
      _ = mu * y i0 := by rw [hyi0]; ring
  refine ⟨t, htpos, hle, le_of_mul_le_mul_right hlam (hy i0), fun hlm => ?_⟩
  subst hlm
  funext j
  by_contra hj
  have hlt : y j < t * z j := lt_of_le_of_ne (hle j) (by simpa using hj)
  have : lam * y i0 < lam * y i0 := by
    calc lam * y i0 = ∑ j, a i0 q j * y j := hqe.symm
      _ < ∑ j, a i0 q j * (t * z j) :=
          Finset.sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (hle j) (hpos i0 q hq j).le)
            ⟨j, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt (hpos i0 q hq j)⟩
      _ = t * ∑ j, a i0 q j * z j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
      _ ≤ t * (lam * z i0) := mul_le_mul_of_nonneg_left hzub htpos.le
      _ = lam * y i0 := by rw [hyi0]; ring
  exact lt_irrefl _ this

lemma pe_exists {N : ℕ} (hN : 0 < N) {Q : Fin N → Type*}
    (a : (i : Fin N) → Q i → Fin N → ℝ) (S : (i : Fin N) → Set (Q i)) (m : ℝ)
    (h : MarkovHyp a S m) :
    ∃ (lam : ℝ) (y : Fin N → ℝ), 0 < lam ∧ (∀ i, 0 < y i) ∧ IsMaxEigenpair a S lam y := by
  classical
  let qm : (Fin N → ℝ) → (i : Fin N) → Q i := fun y i => (h.attain y i).choose
  have qm_mem : ∀ y i, qm y i ∈ S i := fun y i => (h.attain y i).choose_spec.1
  have qm_max : ∀ y i, ∀ q ∈ S i, ∑ j, a i q j * y j ≤ ∑ j, a i (qm y i) j * y j :=
    fun y i => (h.attain y i).choose_spec.2
  let F : (Fin N → ℝ) → Fin N → ℝ := fun y i => ∑ j, a i (qm y i) j * y j
  have hbd : ∀ y y' i, F y i - F y' i ≤ m * ∑ j, |y j - y' j| := by
    intro y y' i
    have h1 := qm_max y' i (qm y i) (qm_mem y i)
    have h2 : ∑ j, a i (qm y i) j * y j - ∑ j, a i (qm y i) j * y' j ≤ m * ∑ j, |y j - y' j| := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      have ha := h.pos i _ (qm_mem y i) j
      have hb := h.bdd i _ (qm_mem y i) j
      rw [← mul_sub]
      calc a i (qm y i) j * (y j - y' j) ≤ a i (qm y i) j * |y j - y' j| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) ha.le
        _ ≤ m * |y j - y' j| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    show ∑ j, a i (qm y i) j * y j - ∑ j, a i (qm y' i) j * y' j ≤ _
    linarith
  have hFc : Continuous F := by
    refine continuous_pi fun i => continuous_iff_continuousAt.2 fun y0 => ?_
    have hg : Filter.Tendsto (fun y : Fin N → ℝ => m * ∑ j, |y j - y0 j|) (nhds y0) (nhds 0) := by
      have hc : Continuous (fun y : Fin N → ℝ => m * ∑ j, |y j - y0 j|) := by fun_prop
      simpa using hc.tendsto y0
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun y => ?_) hg)
    rw [Real.dist_eq, abs_le]
    constructor
    · have := hbd y0 y i
      have e : ∑ j, |y0 j - y j| = ∑ j, |y j - y0 j| :=
        Finset.sum_congr rfl fun j _ => abs_sub_comm _ _
      rw [e] at this; linarith
    · exact hbd y y0 i
  let K : Set (Fin N → ℝ) := {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1}
  have hFpos : ∀ y ∈ K, ∀ i, 0 < F y i := by
    rintro y ⟨hy0, hy1⟩ i
    obtain ⟨j, hj⟩ : ∃ j, 0 < y j := by
      by_contra hc
      push_neg at hc
      have : ∑ i, y i ≤ 0 := Finset.sum_nonpos fun i _ => hc i
      linarith
    exact Finset.sum_pos' (fun k _ => mul_nonneg (h.pos i _ (qm_mem y i) k).le (hy0 k))
      ⟨j, Finset.mem_univ _, mul_pos (h.pos i _ (qm_mem y i) j) hj⟩
  have hsum : ∀ y ∈ K, 0 < ∑ i, F y i := fun y hy =>
    Finset.sum_pos (fun i _ => hFpos y hy i) ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  let G : (Fin N → ℝ) → Fin N → ℝ := fun y => (∑ i, F y i)⁻¹ • F y
  have hKconv : Convex ℝ K := by
    rintro x ⟨hx0, hx1⟩ y ⟨hy0, hy1⟩ s t hs ht hst
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg hs (hx0 i)) (mul_nonneg ht (hy0 i))
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx1, hy1]
      linarith
  have hKclosed : IsClosed K := by
    have e : K = (⋂ i, {y : Fin N → ℝ | 0 ≤ y i}) ∩ {y | ∑ i, y i = 1} := by
      ext y; simp [K]
    rw [e]
    apply IsClosed.inter
    · exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_eq (by fun_prop) continuous_const
  have hKbdd : Bornology.IsBounded K := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin N → ℝ)) (r := 1)).subset ?_
    rintro y ⟨hy0, hy1⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_of_nonneg (hy0 i), ← hy1]
    exact Finset.single_le_sum (fun j _ => hy0 j) (Finset.mem_univ i)
  have hKcpt : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKclosed hKbdd
  have hKne : K.Nonempty := by
    refine ⟨fun _ => (N : ℝ)⁻¹, fun _ => by positivity, ?_⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  have hGc : ContinuousOn G K := by
    show ContinuousOn (fun y => (∑ i, F y i)⁻¹ • F y) K
    refine ContinuousOn.smul (f := fun y => (∑ i, F y i)⁻¹) ?_ hFc.continuousOn
    refine ContinuousOn.inv₀ (by fun_prop) fun y hy => (hsum y hy).ne'
  have hGK : Set.MapsTo G K K := by
    intro y hy
    refine ⟨fun i => ?_, ?_⟩
    · simp only [G, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.2 (hsum y hy).le) (hFpos y hy i).le
    · simp only [G, Pi.smul_apply, smul_eq_mul]
      rw [← Finset.mul_sum, inv_mul_cancel₀ (hsum y hy).ne']
  obtain ⟨y, hyK, hfix⟩ := brouwer_local_fp hKconv hKcpt hKne G hGc hGK
  set s := ∑ i, F y i with hs
  have hspos : 0 < s := hsum y hyK
  have hFy : ∀ i, F y i = s * y i := by
    intro i
    have := congrFun hfix i
    simp only [G, Pi.smul_apply, smul_eq_mul] at this
    rw [← this, ← mul_assoc, mul_inv_cancel₀ hspos.ne', one_mul]
  refine ⟨s, y, hspos, fun i => ?_, fun i => ⟨⟨qm y i, qm_mem y i, hFy i⟩, ?_⟩⟩
  · have := hFpos y hyK i
    rw [hFy i] at this
    exact pos_of_mul_pos_right this hspos.le
  · rintro _ ⟨q, hq, rfl⟩
    rw [← hFy i]
    exact qm_max y i q hq

theorem perron_core {N : ℕ} (hN : 0 < N) {Q : Fin N → Type*}
    (a : (i : Fin N) → Q i → Fin N → ℝ) (S : (i : Fin N) → Set (Q i)) (m : ℝ)
    (h : MarkovHyp a S m) :
    ∃ (lam : ℝ) (y : Fin N → ℝ), 0 < lam ∧ (∀ i, 0 < y i) ∧ IsMaxEigenpair a S lam y ∧
      (∀ (μ : ℝ) (z : Fin N → ℝ), 0 < μ → (∀ i, 0 < z i) → IsMaxEigenpair a S μ z →
        μ = lam ∧ ∃ κ : ℝ, 0 < κ ∧ z = κ • y) ∧
      IsGreatest ((fun q => perronRoot (matOf a q)) '' Set.pi Set.univ S) lam := by
  classical
  obtain ⟨lam, y, hlam, hy, hY⟩ := pe_exists hN a S m h
  refine ⟨lam, y, hlam, hy, hY, fun μ z hμ hz hZ => ?_, ?_⟩
  · obtain ⟨t, ht, -, h1, -⟩ := pe_cmp hN a S h.pos lam μ y z hy hz hY hZ
    obtain ⟨t', ht', -, h2, h3⟩ := pe_cmp hN a S h.pos μ lam z y hz hy hZ hY
    have e : μ = lam := le_antisymm h2 h1
    exact ⟨e, t', ht', h3 e⟩
  · have hup : ∀ q ∈ Set.pi Set.univ S, spectralRadius ℂ ((matOf a q).map (algebraMap ℝ ℂ))
        ≤ ENNReal.ofReal lam := by
      intro q hq
      refine pe_spec_upper _ (fun i j => (h.pos i _ (hq i (Set.mem_univ _)) j).le) y hy lam
        hlam.le fun i => ?_
      simpa [matOf] using (hY i).2 ⟨q i, hq i (Set.mem_univ _), rfl⟩
    let qs : (i : Fin N) → Q i := fun i => ((hY i).1).choose
    have qs_mem : qs ∈ Set.pi Set.univ S := fun i _ => ((hY i).1).choose_spec.1
    have qs_eq : ∀ i, ∑ j, a i (qs i) j * y j = lam * y i := fun i => ((hY i).1).choose_spec.2
    have hlow := pe_spec_lower (matOf a qs) y (fun h0 => (hy ⟨0, hN⟩).ne' (by simp [h0]))
      lam hlam.le (fun i => by simpa [matOf] using qs_eq i)
    refine ⟨⟨qs, qs_mem, ?_⟩, ?_⟩
    · show (spectralRadius ℂ _).toReal = lam
      rw [le_antisymm (hup qs qs_mem) hlow, ENNReal.toReal_ofReal hlam.le]
    · rintro _ ⟨q, hq, rfl⟩
      exact ENNReal.toReal_le_of_le_ofReal hlam.le (hup q hq)

end

section
open BellmanDP.Markovian

theorem solution {N : ℕ} (hN : 0 < N) {Q : Fin N → Type*}
    (a : (i : Fin N) → Q i → Fin N → ℝ) (S : (i : Fin N) → Set (Q i)) (m : ℝ)
    (h : MarkovHyp a S m) :
    ∃ (lam : ℝ) (y : Fin N → ℝ), 0 < lam ∧ (∀ i, 0 < y i) ∧ IsMaxEigenpair a S lam y ∧
      (∀ (μ : ℝ) (z : Fin N → ℝ), 0 < μ → (∀ i, 0 < z i) → IsMaxEigenpair a S μ z →
        μ = lam ∧ ∃ κ : ℝ, 0 < κ ∧ z = κ • y) ∧
      IsGreatest ((fun q => perronRoot (matOf a q)) '' Set.pi Set.univ S) lam := by
  exact perron_core hN a S m h

end
