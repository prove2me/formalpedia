-- Prove2me | solution 4 for ChanPangGQVI.ProjExistence.theorem_5_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:31:16.013477+00:00
-- url     : https://prove2.me/submissions/55418402-66ca-4dff-94ba-a650f65255a2

import Mathlib
import Definitions.Def_ChanPangGQVI_Shared_GQVI
import Theorems.Thm_Brouwer_exists_fixedPoint_closedBall_contDiff

-- carved verbatim out of submission 08ed2756-557a-470f-8493-8c93e6b779c8, lines 936-949

section
open Metric Set MeasureTheory
open ChanPangGQVI

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

theorem brouwer_core {E : Type*} [NormedAddCommGroup E]
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
open Metric Set MeasureTheory
open ChanPangGQVI
open Filter Topology
open scoped RealInnerProductSpace

def IsVProj {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) (z p : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  p ∈ S ∧ ∀ w ∈ S, ⟪z - p, w - p⟫ ≤ 0

theorem exists_vproj {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))} (hne : S.Nonempty)
    (hcl : IsClosed S) (hcv : Convex ℝ S) (z : EuclideanSpace ℝ (Fin n)) :
    ∃ p, IsVProj S z p := by
  obtain ⟨v, hv, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hcv z
  exact ⟨v, hv, (norm_eq_iInf_iff_real_inner_le_zero hcv hv).1 hmin⟩

theorem vproj_unique {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    {z p q : EuclideanSpace ℝ (Fin n)} (hp : IsVProj S z p) (hq : IsVProj S z q) : p = q := by
  have h1 := hp.2 q hq.1
  have h2 := hq.2 p hp.1
  have e1 : ⟪z - q, p - q⟫ = -⟪z - q, q - p⟫ := by
    rw [← inner_neg_right, neg_sub]
  have e2 : ⟪z - p, q - p⟫ - ⟪z - q, q - p⟫ = ⟪q - p, q - p⟫ := by
    rw [← inner_sub_left]
    congr 1
    abel
  have h3 : ⟪q - p, q - p⟫ ≤ 0 := by linarith
  have h4 : q - p = 0 := real_inner_self_nonpos.1 h3
  exact (sub_eq_zero.1 h4).symm

theorem vproj_le_infDist {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    {z p : EuclideanSpace ℝ (Fin n)} (hp : IsVProj S z p) (w : EuclideanSpace ℝ (Fin n)) :
    ⟪z - p, w - p⟫ ≤ ‖z - p‖ * infDist w S := by
  have hne : S.Nonempty := ⟨p, hp.1⟩
  by_cases h0 : ‖z - p‖ = 0
  · have hz : z - p = 0 := norm_eq_zero.1 h0
    simp [hz]
  have hpos : 0 < ‖z - p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have key : ⟪z - p, w - p⟫ / ‖z - p‖ ≤ infDist w S := by
    rw [le_infDist hne]
    intro w' hw'
    rw [div_le_iff₀' hpos]
    have h1 := hp.2 w' hw'
    have e : ⟪z - p, w - p⟫ = ⟪z - p, w' - p⟫ + ⟪z - p, w - w'⟫ := by
      rw [← inner_add_right]
      congr 1
      abel
    have h2 : ⟪z - p, w - w'⟫ ≤ ‖z - p‖ * ‖w - w'‖ := real_inner_le_norm _ _
    rw [dist_eq_norm]
    linarith
  rwa [div_le_iff₀' hpos] at key

theorem thm52_core {n : ℕ}
    (K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C) (hC_convex : Convex ℝ C)
    (h_i : ∀ x ∈ C, K x ⊆ C)
    (h_ii : ContinuousOn f C)
    (h_iii_nonempty : ∀ x ∈ C, (K x).Nonempty)
    (h_iii_upper : UpperHemicontinuousOn K C) (h_iii_lower : LowerHemicontinuousOn K C)
    (h_iii_convex : ∀ x ∈ C, Convex ℝ (K x))
    (hK_closed : ∀ x ∈ C, IsClosed (K x)) :
    ∃ x y, ChanPangGQVI.Shared.IsGQVISolution K (fun z => {f z}) x y := by
  classical
  have hex : ∀ x ∈ C, ∃ p, IsVProj (K x) (x - f x) p := fun x hx =>
    exists_vproj (h_iii_nonempty x hx) (hK_closed x hx) (h_iii_convex x hx) _
  let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun x => if h : x ∈ C then (hex x h).choose else x
  have hg : ∀ x ∈ C, IsVProj (K x) (x - f x) (g x) := by
    intro x hx
    simp only [g, dif_pos hx]
    exact (hex x hx).choose_spec
  have hmaps : MapsTo g C C := fun x hx => h_i x hx (hg x hx).1
  have hcont : ContinuousOn g C := by
    intro x0 hx0
    apply hC_compact.tendsto_nhds_of_unique_mapClusterPt
      (eventually_nhdsWithin_of_forall hmaps)
    intro p _ hclp
    set l := 𝓝[C] x0 with hl
    set F := l ⊓ comap g (𝓝 p) with hF
    have : F.NeBot := by
      rw [inf_neBot_iff]
      intro a ha b hb
      obtain ⟨t, ht, htb⟩ := mem_comap.1 hb
      have hfr := (mapClusterPt_iff_frequently.1 hclp) t ht
      obtain ⟨x, hxt, hxa⟩ := (hfr.and_eventually ha).exists
      exact ⟨x, hxa, htb hxt⟩
    have hFl : F ≤ l := inf_le_left
    have hgF : Tendsto g F (𝓝 p) := tendsto_comap.mono_left inf_le_right
    have hxF : Tendsto (fun x => x) F (𝓝 x0) :=
      tendsto_id.mono_left (hFl.trans nhdsWithin_le_nhds)
    have hfF : Tendsto f F (𝓝 (f x0)) := (h_ii x0 hx0).tendsto.mono_left hFl
    have hzF : Tendsto (fun x => x - f x) F (𝓝 (x0 - f x0)) := hxF.sub hfF
    have hCF : ∀ᶠ x in F, x ∈ C := hFl self_mem_nhdsWithin
    have hne0 := h_iii_nonempty x0 hx0
    -- (a) the limit point lies in `K x0`
    have hpK : p ∈ K x0 := by
      by_contra hp
      have hpos : 0 < infDist p (K x0) := by
        rw [← infDist_pos_iff_notMem_closure hne0, (hK_closed x0 hx0).closure_eq]
        exact hp
      set r := infDist p (K x0) with hr
      have ht : thickening (r / 2) (K x0) ∈ 𝓝ˢ (K x0) :=
        isOpen_thickening.mem_nhdsSet.2 (self_subset_thickening (by linarith) _)
      have hev : ∀ᶠ x in l, thickening (r / 2) (K x0) ∈ 𝓝ˢ (K x) :=
        upperHemicontinuousWithinAt_iff.1 (upperHemicontinuousOn_iff.1 h_iii_upper x0 hx0) _ ht
      have hev2 : ∀ᶠ x in F, infDist (g x) (K x0) < r / 2 := by
        filter_upwards [hFl hev, hCF] with x hx hxC
        have hmem := subset_of_mem_nhdsSet hx (hg x hxC).1
        exact (mem_thickening_iff_infDist_lt hne0).1 hmem
      have hlim : Tendsto (fun x => infDist (g x) (K x0)) F (𝓝 r) :=
        ((continuous_infDist_pt (K x0)).tendsto p).comp hgF
      have : r ≤ r / 2 := le_of_tendsto hlim (hev2.mono fun x hx => hx.le)
      linarith
    -- (b) the variational inequality passes to the limit
    have hVI : ∀ w ∈ K x0, ⟪(x0 - f x0) - p, w - p⟫ ≤ 0 := by
      intro w hw
      have hd : Tendsto (fun x => infDist w (K x)) F (𝓝 0) := by
        rw [Metric.tendsto_nhds]
        intro ε hε
        have hev : ∀ᶠ x in l, (K x ∩ ball w ε).Nonempty :=
          lowerHemicontinuousWithinAt_iff.1 (lowerHemicontinuousOn_iff.1 h_iii_lower x0 hx0)
            _ isOpen_ball ⟨w, hw, mem_ball_self hε⟩
        filter_upwards [hFl hev] with x hx
        obtain ⟨y, hyK, hyb⟩ := hx
        have h0 : 0 ≤ infDist w (K x) := infDist_nonneg
        rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
        calc infDist w (K x) ≤ dist w y := infDist_le_dist_of_mem hyK
          _ < ε := by rw [dist_comm]; exact hyb
      have hineq : ∀ᶠ x in F,
          ⟪(x - f x) - g x, w - g x⟫ ≤ ‖(x - f x) - g x‖ * infDist w (K x) := by
        filter_upwards [hCF] with x hx
        exact vproj_le_infDist (hg x hx) w
      have hL1 : Tendsto (fun x => ⟪(x - f x) - g x, w - g x⟫) F
          (𝓝 ⟪(x0 - f x0) - p, w - p⟫) :=
        (hzF.sub hgF).inner (tendsto_const_nhds.sub hgF)
      have hR : Tendsto (fun x => ‖(x - f x) - g x‖ * infDist w (K x)) F
          (𝓝 (‖(x0 - f x0) - p‖ * 0)) :=
        (hzF.sub hgF).norm.mul hd
      rw [mul_zero] at hR
      exact le_of_tendsto_of_tendsto hL1 hR hineq
    exact vproj_unique ⟨hpK, hVI⟩ (hg x0 hx0)
  obtain ⟨x, hxC, hfx⟩ := brouwer_core hC_convex hC_compact hC_nonempty g hcont hmaps
  have hx := hg x hxC
  rw [hfx] at hx
  refine ⟨x, f x, hx.1, rfl, ?_⟩
  intro x' hx'
  have h1 := hx.2 x' hx'
  have e : (x - f x) - x = -(f x) := by abel
  rw [e, inner_neg_left, real_inner_comm] at h1
  linarith

end

section
open Metric Set MeasureTheory

theorem solution {n : ℕ}
    (K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C) (hC_convex : Convex ℝ C)
    (h_i : ∀ x ∈ C, K x ⊆ C)
    (h_ii : ContinuousOn f C)
    (h_iii_nonempty : ∀ x ∈ C, (K x).Nonempty)
    (h_iii_upper : UpperHemicontinuousOn K C) (h_iii_lower : LowerHemicontinuousOn K C)
    (h_iii_convex : ∀ x ∈ C, Convex ℝ (K x))
    (hK_closed : ∀ x ∈ C, IsClosed (K x)) :
    ∃ x y, ChanPangGQVI.Shared.IsGQVISolution K (fun z => {f z}) x y := by
  exact thm52_core K f C hC_nonempty hC_compact hC_convex h_i h_ii h_iii_nonempty h_iii_upper h_iii_lower h_iii_convex hK_closed

end
