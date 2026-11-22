-- Prove2me | solution 1 for FuzzyGames.NTUCore.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:03:14.597778+00:00
-- url     : https://prove2.me/submissions/07c8857d-8324-4b3e-9fe5-d45620c37c31

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic
import Theorems.Thm_FuzzyGames_NTUCore_theorem_3_1
import Theorems.Thm_FuzzyGames_NTUCore_support_concave
import Theorems.Thm_FanGlicksberg_kakutani_fan_glicksberg

open Set Finset Pointwise FuzzyGames.NTUCore

/-! ### Basic geometric and algebraic helpers -/

private lemma coal_mem_orthant {n : ℕ} (A : Finset (Fin n)) : coal A ∈ orthant n := by
  intro i
  simp [coal]
  split_ifs <;> norm_num

private lemma zero_mem_orthant {n : ℕ} : (0 : Fin n → ℝ) ∈ orthant n :=
  fun _ => le_rfl

private lemma coal_univ_apply {n : ℕ} (i : Fin n) : coal (Finset.univ : Finset (Fin n)) i = 1 := by
  simp [coal]

private lemma coal_singleton_apply {n : ℕ} (i j : Fin n) :
    coal ({i} : Finset (Fin n)) j = if j = i then 1 else 0 := by
  simp [coal]

private lemma zero_mem_Rtau {n : ℕ} (τ : Fin n → ℝ) : (0 : Fin n → ℝ) ∈ Rtau τ :=
  fun _ _ => rfl

private lemma zero_mem_RtauNonneg {n : ℕ} (τ : Fin n → ℝ) : (0 : Fin n → ℝ) ∈ RtauNonneg τ :=
  ⟨zero_mem_Rtau τ, fun _ => le_rfl⟩

private lemma isClosed_RtauNonneg {n : ℕ} (τ : Fin n → ℝ) : IsClosed (RtauNonneg τ) := by
  have h1 : IsClosed (Rtau τ) := by
    have : Rtau τ = ⋂ i : Fin n, if τ i = 0 then {c : Fin n → ℝ | c i = 0} else Set.univ := by
      ext c
      simp only [Rtau, mem_ofPred_eq, mem_iInter]
      constructor
      · intro hc i
        split_ifs with h
        · exact hc i h
        · trivial
      · intro hc i hi
        have hci := hc i
        simp [hi] at hci
        exact hci
    rw [this]
    refine isClosed_iInter fun i => ?_
    split_ifs
    · exact isClosed_eq (continuous_apply i) continuous_const
    · exact isClosed_univ
  have h2 : IsClosed {c : Fin n → ℝ | ∀ i, 0 ≤ c i} := by
    have : {c : Fin n → ℝ | ∀ i, 0 ≤ c i} = ⋂ i : Fin n, {c : Fin n → ℝ | 0 ≤ c i} := by
      ext c; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  exact h1.inter h2

private lemma convex_RtauNonneg {n : ℕ} (τ : Fin n → ℝ) : Convex ℝ (RtauNonneg τ) := by
  intro x hx y hy a b ha hb _
  refine ⟨fun i hi => ?_, fun i => ?_⟩
  · simp [hx.1 i hi, hy.1 i hi]
  · exact add_nonneg (mul_nonneg ha (hx.2 i)) (mul_nonneg hb (hy.2 i))

private lemma add_mem_RtauNonneg_of_add {n : ℕ} {τ σ x y : Fin n → ℝ}
    (hτ : τ ∈ orthant n) (hσ : σ ∈ orthant n)
    (hx : x ∈ RtauNonneg τ) (hy : y ∈ RtauNonneg σ) :
    x + y ∈ RtauNonneg (τ + σ) := by
  refine ⟨fun i hi => ?_, fun i => add_nonneg (hx.2 i) (hy.2 i)⟩
  have hτi : 0 ≤ τ i := hτ i
  have hσi : 0 ≤ σ i := hσ i
  have hτ0 : τ i = 0 := by linarith [show τ i + σ i = 0 from hi]
  have hσ0 : σ i = 0 := by linarith [show τ i + σ i = 0 from hi]
  simp [hx.1 i hτ0, hy.1 i hσ0]

private lemma isClosed_sub_of_isCompact_isClosed {n : ℕ} {K R : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hR : IsClosed R) : IsClosed (K - R) := by
  rw [← isSeqClosed_iff_isClosed]
  intro u z hu hz
  have hkr : ∀ m, ∃ k ∈ K, ∃ r ∈ R, k - r = u m := by
    intro m
    rcases hu m with ⟨k, hk, r, hr, hkr⟩
    exact ⟨k, hk, r, hr, hkr⟩
  choose k hk r hr hsub using hkr
  obtain ⟨k0, hk0, φ, hφ, hktend⟩ := hK.tendsto_subseq hk
  have hutend : Filter.Tendsto (u ∘ φ) Filter.atTop (nhds z) := hz.comp hφ.tendsto_atTop
  have hrtend : Filter.Tendsto (r ∘ φ) Filter.atTop (nhds (k0 - z)) := by
    have h1 : (fun m => k (φ m) - u (φ m)) = r ∘ φ := by
      ext m i
      have := congr_fun (hsub (φ m)) i
      simp only [Pi.sub_apply, Function.comp_apply] at this ⊢
      linarith
    rw [← h1]
    exact hktend.sub hutend
  have hr0 : k0 - z ∈ R := hR.mem_of_tendsto hrtend (Filter.Eventually.of_forall fun m => hr (φ m))
  refine ⟨k0, hk0, k0 - z, hr0, ?_⟩
  ext i
  simp

private lemma zero_mem_V_zero {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hV : IsNTUFuzzyGame V) : (0 : Fin n → ℝ) ∈ V 0 := by
  obtain ⟨c, hc⟩ := hV.nonempty 0 zero_mem_orthant
  have h0 : c = 0 := by
    ext i
    exact hV.subset_Rtau 0 zero_mem_orthant hc i rfl
  rwa [h0] at hc

/-! ### Step 1: Shifting by singleton maxima so `0 ∈ V τ` and `c i ≤ 0` on `V (coal {i})` -/

private lemma exists_singleton_max {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hV : IsNTUFuzzyGame V) (i : Fin n) :
    ∃ a : ℝ, Pi.single i a ∈ V (coal {i}) ∧ ∀ c ∈ V (coal {i}), c i ≤ a := by
  let S : Set ℝ := {r : ℝ | Pi.single i r ∈ V (coal {i})}
  have hne : S.Nonempty := by
    obtain ⟨c, hc⟩ := hV.nonempty (coal {i}) (coal_mem_orthant {i})
    refine ⟨c i, ?_⟩
    have hceq : Pi.single i (c i) = c := by
      ext j
      by_cases hji : j = i
      · subst hji; simp
      · simp only [Pi.single_eq_of_ne hji]
        exact (hV.subset_Rtau (coal {i}) (coal_mem_orthant {i}) hc j (by simp [coal, hji])).symm
    change Pi.single i (c i) ∈ V (coal {i})
    rwa [hceq]
  have hbdd : BddAbove S := by
    obtain ⟨C, _, hC⟩ := hV.bddAbove (coal {i}) (coal_mem_orthant {i})
    refine ⟨C i, fun r hr => ?_⟩
    rcases hC hr with ⟨c', hc', u, hu, hcu⟩
    rw [mem_singleton_iff] at hc'
    rw [hc'] at hcu
    have h1 := congr_fun hcu i
    simp only [Pi.sub_apply, Pi.single_eq_same] at h1
    linarith [hu.2 i]
  have hcont_single : Continuous (fun r : ℝ => (Pi.single i r : Fin n → ℝ)) := by
    refine continuous_pi fun j => ?_
    by_cases hji : j = i
    · subst hji
      simp only [Pi.single_eq_same]
      exact continuous_id
    · simp only [Pi.single_eq_of_ne hji]
      exact continuous_const
  have hclosed : IsClosed S :=
    (hV.isClosed (coal {i}) (coal_mem_orthant {i})).preimage hcont_single
  refine ⟨sSup S, hclosed.csSup_mem hne hbdd, fun c hc => ?_⟩
  have hcmem : c i ∈ S := by
    have hceq : Pi.single i (c i) = c := by
      ext j
      by_cases hji : j = i
      · subst hji; simp
      · simp only [Pi.single_eq_of_ne hji]
        exact (hV.subset_Rtau (coal {i}) (coal_mem_orthant {i}) hc j (by simp [coal, hji])).symm
    change Pi.single i (c i) ∈ V (coal {i})
    rwa [hceq]
  exact le_csSup hbdd hcmem

private lemma tmul_a_mem {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hV : IsNTUFuzzyGame V) (hsup : Superadditive V)
    {a : Fin n → ℝ} (ha : ∀ i, Pi.single i (a i) ∈ V (coal {i}))
    {τ : Fin n → ℝ} (hτ : τ ∈ orthant n) : tmul τ a ∈ V τ := by
  have hterm : ∀ i : Fin n, Pi.single i (τ i * a i) ∈ V (τ i • coal {i}) := by
    intro i
    have hτi : (0 : ℝ) ≤ τ i := hτ i
    rcases hτi.eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul, zero_smul, Pi.single_zero]
      exact zero_mem_V_zero hV
    · rw [hV.homogeneous (τ i) hpos (coal {i}) (coal_mem_orthant {i})]
      refine ⟨Pi.single i (a i), ha i, ?_⟩
      ext j
      by_cases hji : j = i
      · subst hji; simp
      · simp [Pi.single_eq_of_ne hji]
  have hsum : ∀ s : Finset (Fin n),
      (∑ i ∈ s, Pi.single i (τ i * a i)) ∈ V (∑ i ∈ s, τ i • coal {i}) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact zero_mem_V_zero hV
    | @insert j s hjs ih =>
      rw [Finset.sum_insert hjs, Finset.sum_insert hjs]
      have h1 : τ j • coal {j} ∈ orthant n := fun k => mul_nonneg (hτ j) (coal_mem_orthant {j} k)
      have h2 : ∑ i ∈ s, τ i • coal {i} ∈ orthant n := by
        intro k
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_nonneg fun i _ => mul_nonneg (hτ i) (coal_mem_orthant {i} k)
      exact hsup _ h1 _ h2 (Set.add_mem_add (hterm j) ih)
  have h1 : (∑ i : Fin n, Pi.single i (τ i * a i)) = tmul τ a := by
    ext j
    simp [tmul, Finset.sum_apply, Pi.single_apply]
  have h2 : (∑ i : Fin n, τ i • coal {i}) = τ := by
    ext j
    simp [coal, Finset.sum_apply]
  simpa only [h1, h2] using hsum Finset.univ

private def shiftGame {n : ℕ} (V : (Fin n → ℝ) → Set (Fin n → ℝ)) (a : Fin n → ℝ)
    (τ : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {y | y + tmul τ a ∈ V τ}

private lemma shiftGame_isNTUFuzzyGame {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hV : IsNTUFuzzyGame V) (hsup : Superadditive V)
    {a : Fin n → ℝ} (ha : ∀ i, Pi.single i (a i) ∈ V (coal {i})) :
    IsNTUFuzzyGame (shiftGame V a) where
  subset_Rtau := by
    intro τ hτ y hy i hi
    have h1 := hV.subset_Rtau τ hτ hy i hi
    simp [tmul, hi] at h1
    exact h1
  nonempty := by
    intro τ hτ
    refine ⟨0, ?_⟩
    change 0 + tmul τ a ∈ V τ
    rw [zero_add]
    exact tmul_a_mem hV hsup ha hτ
  isClosed := by
    intro τ hτ
    exact (hV.isClosed τ hτ).preimage (continuous_id.add continuous_const)
  convex := by
    intro τ hτ x hx y hy s t hs ht hst
    change (s • x + t • y) + tmul τ a ∈ V τ
    have hEq : (s • x + t • y) + tmul τ a = s • (x + tmul τ a) + t • (y + tmul τ a) := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc s * x i + t * y i + tmul τ a i
          = s * x i + t * y i + (s + t) * tmul τ a i := by rw [hst, one_mul]
        _ = s * (x i + tmul τ a i) + t * (y i + tmul τ a i) := by ring
    rw [hEq]
    exact hV.convex τ hτ hx hy hs ht hst
  comprehensive := by
    intro τ hτ
    ext y
    constructor
    · rintro ⟨x, hx, u, hu, rfl⟩
      change (x - u) + tmul τ a ∈ V τ
      have hEq : (x - u) + tmul τ a = (x + tmul τ a) - u := by abel
      rw [hEq, ← hV.comprehensive τ hτ]
      exact ⟨x + tmul τ a, hx, u, hu, rfl⟩
    · intro hy
      exact ⟨y, hy, 0, zero_mem_RtauNonneg τ, sub_zero y⟩
  bddAbove := by
    intro τ hτ
    obtain ⟨C, hCR, hC⟩ := hV.bddAbove τ hτ
    refine ⟨C - tmul τ a, fun i hi => by simp [hCR i hi, tmul, hi], ?_⟩
    intro y hy
    rcases hC hy with ⟨c', hc', u, hu, hcu⟩
    rw [mem_singleton_iff] at hc'
    rw [hc'] at hcu
    refine ⟨C - tmul τ a, mem_singleton _, u, hu, ?_⟩
    ext i
    have h1 := congr_fun hcu i
    simp only [Pi.sub_apply, Pi.add_apply] at h1 ⊢
    linarith
  homogeneous := by
    intro t ht τ hτ
    ext y
    constructor
    · intro hy
      change y + tmul (t • τ) a ∈ V (t • τ) at hy
      rw [hV.homogeneous t ht τ hτ] at hy
      rcases hy with ⟨z, hz, hzy⟩
      refine ⟨z - tmul τ a, ?_, ?_⟩
      · change (z - tmul τ a) + tmul τ a ∈ V τ
        rwa [sub_add_cancel]
      · ext i
        have h1 := congr_fun hzy i
        simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, tmul] at h1 ⊢
        linarith
    · rintro ⟨z, hz, rfl⟩
      change t • z + tmul (t • τ) a ∈ V (t • τ)
      rw [hV.homogeneous t ht τ hτ]
      refine ⟨z + tmul τ a, hz, ?_⟩
      ext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, tmul]
      ring

private lemma shiftGame_superadditive {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hsup : Superadditive V) (a : Fin n → ℝ) :
    Superadditive (shiftGame V a) := by
  intro τ hτ σ hσ z hz
  rcases hz with ⟨x, hx, y, hy, rfl⟩
  change (x + y) + tmul (τ + σ) a ∈ V (τ + σ)
  have hEq : (x + y) + tmul (τ + σ) a = (x + tmul τ a) + (y + tmul σ a) := by
    ext i
    simp only [Pi.add_apply, tmul]
    ring
  rw [hEq]
  exact hsup τ hτ σ hσ (Set.add_mem_add hx hy)

private lemma shiftGame_core_add {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    {a c : Fin n → ℝ} (hc : c ∈ fuzzyCore (shiftGame V a)) :
    c + a ∈ fuzzyCore V := by
  refine ⟨?_, ?_⟩
  · have h1 : c + tmul (coal Finset.univ) a ∈ V (coal Finset.univ) := hc.1
    have h2 : tmul (coal Finset.univ) a = a := by
      ext i; simp [tmul, coal]
    rwa [h2] at h1
  · intro τ hτ hτ0 hmem
    rcases hmem with ⟨z, hz, u, hu, hzu⟩
    apply hc.2 τ hτ hτ0
    refine ⟨z - tmul τ a, ?_, u, hu, ?_⟩
    · change (z - tmul τ a) + tmul τ a ∈ V τ
      rwa [sub_add_cancel]
    · ext i
      have h1 := congr_fun hzu i
      simp only [Pi.sub_apply, Pi.add_apply, tmul] at h1 ⊢
      linarith

/-! ### Step 2: Truncated game `W(τ) = (V(τ) ∩ RtauNonneg τ) - RtauNonneg τ` -/

private def Kset {n : ℕ} (V : (Fin n → ℝ) → Set (Fin n → ℝ)) (τ : Fin n → ℝ) : Set (Fin n → ℝ) :=
  V τ ∩ RtauNonneg τ

private def Wgame {n : ℕ} (V : (Fin n → ℝ) → Set (Fin n → ℝ)) (τ : Fin n → ℝ) : Set (Fin n → ℝ) :=
  Kset V τ - RtauNonneg τ

private lemma zero_mem_Kset {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (h0 : ∀ τ ∈ orthant n, (0 : Fin n → ℝ) ∈ V τ) {τ : Fin n → ℝ} (hτ : τ ∈ orthant n) :
    (0 : Fin n → ℝ) ∈ Kset V τ :=
  ⟨h0 τ hτ, zero_mem_RtauNonneg τ⟩

private lemma Kset_isCompact {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hV : IsNTUFuzzyGame V) {τ : Fin n → ℝ} (hτ : τ ∈ orthant n) :
    IsCompact (Kset V τ) := by
  obtain ⟨C, _, hC⟩ := hV.bddAbove τ hτ
  have hsub : Kset V τ ⊆ Set.Icc 0 C := by
    intro x hx
    refine ⟨fun i => hx.2.2 i, fun i => ?_⟩
    rcases hC hx.1 with ⟨c', hc', u, hu, hcu⟩
    rw [mem_singleton_iff] at hc'
    subst hc'
    have h1 := congr_fun hcu i
    simp only [Pi.sub_apply] at h1
    linarith [hu.2 i]
  exact isCompact_Icc.of_isClosed_subset ((hV.isClosed τ hτ).inter (isClosed_RtauNonneg τ)) hsub

private lemma Kset_convex {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hV : IsNTUFuzzyGame V) {τ : Fin n → ℝ} (hτ : τ ∈ orthant n) :
    Convex ℝ (Kset V τ) :=
  (hV.convex τ hτ).inter (convex_RtauNonneg τ)

private lemma Wgame_subset {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hV : IsNTUFuzzyGame V) {τ : Fin n → ℝ} (hτ : τ ∈ orthant n) :
    Wgame V τ ⊆ V τ := by
  intro x hx
  rcases hx with ⟨k, hk, u, hu, rfl⟩
  rw [← hV.comprehensive τ hτ]
  exact ⟨k, hk.1, u, hu, rfl⟩

private lemma Wgame_isNTUFuzzyGame {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hV : IsNTUFuzzyGame V) (h0 : ∀ τ ∈ orthant n, (0 : Fin n → ℝ) ∈ V τ) :
    IsNTUFuzzyGame (Wgame V) where
  subset_Rtau := fun τ hτ => (Wgame_subset hV hτ).trans (hV.subset_Rtau τ hτ)
  nonempty := fun τ hτ => ⟨0, ⟨0, zero_mem_Kset h0 hτ, 0, zero_mem_RtauNonneg τ, sub_zero 0⟩⟩
  isClosed := fun τ hτ => isClosed_sub_of_isCompact_isClosed (Kset_isCompact hV hτ) (isClosed_RtauNonneg τ)
  convex := fun τ hτ => (Kset_convex hV hτ).sub (convex_RtauNonneg τ)
  comprehensive := by
    intro τ hτ
    ext x
    constructor
    · rintro ⟨w, ⟨k, hk, u, hu, rfl⟩, v, hv, rfl⟩
      refine ⟨k, hk, u + v, ⟨fun i hi => by simp [hu.1 i hi, hv.1 i hi],
        fun i => add_nonneg (hu.2 i) (hv.2 i)⟩, ?_⟩
      ext i; simp only [Pi.sub_apply, Pi.add_apply]; ring
    · intro hx
      exact ⟨x, hx, 0, zero_mem_RtauNonneg τ, sub_zero x⟩
  bddAbove := by
    intro τ hτ
    obtain ⟨C, hCR, hC⟩ := hV.bddAbove τ hτ
    exact ⟨C, hCR, (Wgame_subset hV hτ).trans hC⟩
  homogeneous := by
    intro t ht τ hτ
    have hRtau : Rtau (t • τ) = Rtau τ := by
      ext c
      simp only [Rtau, mem_ofPred_eq, Pi.smul_apply, smul_eq_mul]
      exact forall_congr' fun i => by rw [mul_eq_zero, or_iff_right ht.ne']
    have hRnn : RtauNonneg (t • τ) = RtauNonneg τ := by
      ext c
      simp only [RtauNonneg, mem_ofPred_eq, hRtau]
    have hKeq : Kset V (t • τ) = t • Kset V τ := by
      ext x
      simp only [Kset, mem_inter_iff, hV.homogeneous t ht τ hτ, hRnn, mem_smul_set]
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hxnn⟩
        refine ⟨z, ⟨hz, ⟨fun i hi => ?_, fun i => ?_⟩⟩, rfl⟩
        · have h1 := hxnn.1 i hi
          simp only [Pi.smul_apply, smul_eq_mul, mul_eq_zero, ht.ne', false_or] at h1
          exact h1
        · have h1 := hxnn.2 i
          simp only [Pi.smul_apply, smul_eq_mul] at h1
          exact nonneg_of_mul_nonneg_right h1 ht
      · rintro ⟨z, ⟨hz, hznn⟩, rfl⟩
        refine ⟨⟨z, hz, rfl⟩, ⟨fun i hi => ?_, fun i => ?_⟩⟩
        · simp [hznn.1 i hi]
        · exact mul_nonneg ht.le (hznn.2 i)
    ext x
    simp only [Wgame, hKeq, hRnn, Set.mem_sub, mem_smul_set]
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, u, hu, rfl⟩
      refine ⟨k - t⁻¹ • u, ⟨k, hk, t⁻¹ • u, ⟨fun i hi => by simp [hu.1 i hi],
        fun i => mul_nonneg (inv_nonneg.2 ht.le) (hu.2 i)⟩, rfl⟩, ?_⟩
      ext i
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp [ht.ne']
    · rintro ⟨_, ⟨k, hk, u, hu, rfl⟩, rfl⟩
      refine ⟨t • k, ⟨k, hk, rfl⟩, t • u, ⟨fun i hi => by simp [hu.1 i hi],
        fun i => mul_nonneg ht.le (hu.2 i)⟩, ?_⟩
      ext i
      simp [mul_sub]

private lemma Wgame_superadditive {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hsup : Superadditive V) : Superadditive (Wgame V) := by
  intro τ hτ σ hσ z hz
  rcases hz with ⟨_, ⟨k1, hk1, u1, hu1, rfl⟩, _, ⟨k2, hk2, u2, hu2, rfl⟩, rfl⟩
  refine ⟨k1 + k2, ⟨hsup τ hτ σ hσ (Set.add_mem_add hk1.1 hk2.1),
    add_mem_RtauNonneg_of_add hτ hσ hk1.2 hk2.2⟩,
    u1 + u2, add_mem_RtauNonneg_of_add hτ hσ hu1 hu2, ?_⟩
  ext i; simp only [Pi.sub_apply, Pi.add_apply]; ring

/-! ### Support function `wval` of `Wgame` -/

private noncomputable def wval {n : ℕ} (V : (Fin n → ℝ) → Set (Fin n → ℝ))
    (τ l : Fin n → ℝ) : ℝ :=
  (supportFn (Wgame V τ) l).toReal

private lemma wval_spec {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hV : IsNTUFuzzyGame V) (h0 : ∀ τ ∈ orthant n, (0 : Fin n → ℝ) ∈ V τ)
    {τ l : Fin n → ℝ} (hτ : τ ∈ orthant n) (hl : l ∈ orthant n) :
    (∃ z ∈ Kset V τ, ∑ i, l i * z i = wval V τ l) ∧
    (∀ x ∈ Wgame V τ, ∑ i, l i * x i ≤ wval V τ l) ∧
    supportFn (Wgame V τ) l = ((wval V τ l : ℝ) : EReal) := by
  have hKcomp := Kset_isCompact hV hτ
  have hKne : (Kset V τ).Nonempty := ⟨0, zero_mem_Kset h0 hτ⟩
  have hcont : Continuous (fun z : Fin n → ℝ => ∑ i, l i * z i) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)
  obtain ⟨z0, hz0K, hz0max⟩ := hKcomp.exists_isMaxOn hKne hcont.continuousOn
  set M : ℝ := ∑ i, l i * z0 i
  have hleW : ∀ x ∈ Wgame V τ, ∑ i, l i * x i ≤ M := by
    rintro x ⟨k, hk, u, hu, rfl⟩
    have h1 : ∑ i, l i * (k i - u i) = (∑ i, l i * k i) - ∑ i, l i * u i := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
    have h2 : 0 ≤ ∑ i, l i * u i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (hu.2 i)
    have h3 : ∑ i, l i * k i ≤ M := hz0max hk
    change ∑ i, l i * (k i - u i) ≤ M
    linarith
  have hsup_eq : supportFn (Wgame V τ) l = (M : EReal) := by
    apply le_antisymm
    · refine iSup₂_le fun x hx => ?_
      exact EReal.coe_le_coe_iff.2 (hleW x hx)
    · have hz0W : z0 ∈ Wgame V τ := ⟨z0, hz0K, 0, zero_mem_RtauNonneg τ, sub_zero z0⟩
      exact le_iSup₂_of_le z0 hz0W le_rfl
  have hwval_eq : wval V τ l = M := by
    simp [wval, hsup_eq]
  rw [hwval_eq]
  exact ⟨⟨z0, hz0K, rfl⟩, hleW, hsup_eq⟩

private lemma wval_nonneg {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hV : IsNTUFuzzyGame V) (h0 : ∀ τ ∈ orthant n, (0 : Fin n → ℝ) ∈ V τ)
    {τ l : Fin n → ℝ} (hτ : τ ∈ orthant n) (hl : l ∈ orthant n) :
    0 ≤ wval V τ l := by
  have hspec := wval_spec hV h0 hτ hl
  have h0W : (0 : Fin n → ℝ) ∈ Wgame V τ :=
    ⟨0, zero_mem_Kset h0 hτ, 0, zero_mem_RtauNonneg τ, sub_zero 0⟩
  simpa using hspec.2.1 0 h0W

private lemma wval_zero {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hV : IsNTUFuzzyGame V) (h0 : ∀ τ ∈ orthant n, (0 : Fin n → ℝ) ∈ V τ)
    {l : Fin n → ℝ} (hl : l ∈ orthant n) :
    wval V 0 l = 0 := by
  obtain ⟨z, hzK, hzeq⟩ := (wval_spec hV h0 zero_mem_orthant hl).1
  have hz0 : z = 0 := by ext i; exact hzK.2.1 i rfl
  rw [← hzeq, hz0]
  simp

private lemma wval_singleton {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hV : IsNTUFuzzyGame V) (h0 : ∀ τ ∈ orthant n, (0 : Fin n → ℝ) ∈ V τ)
    (h1 : ∀ i, ∀ c ∈ V (coal {i}), c i ≤ 0)
    (i : Fin n) {l : Fin n → ℝ} (hl : l ∈ orthant n) :
    wval V (coal {i}) l = 0 := by
  obtain ⟨z, hzK, hzeq⟩ := (wval_spec hV h0 (coal_mem_orthant {i}) hl).1
  have hz0 : z = 0 := by
    ext j
    by_cases hji : j = i
    · subst hji
      exact le_antisymm (h1 j z hzK.1) (hzK.2.2 j)
    · exact hzK.2.1 j (by simp [coal, hji])
  rw [← hzeq, hz0]
  simp

private lemma wval_smul {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hV : IsNTUFuzzyGame V) (h0 : ∀ τ ∈ orthant n, (0 : Fin n → ℝ) ∈ V τ)
    {t : ℝ} (ht : 0 < t) {τ l : Fin n → ℝ} (hτ : τ ∈ orthant n) (hl : l ∈ orthant n) :
    wval V (t • τ) l = t * wval V τ l := by
  have htτ : t • τ ∈ orthant n := fun i => mul_nonneg ht.le (hτ i)
  have hW := Wgame_isNTUFuzzyGame hV h0
  have h1 := wval_spec hV h0 htτ hl
  have h2 := wval_spec hV h0 hτ hl
  obtain ⟨z1, hz1K, hz1eq⟩ := h1.1
  obtain ⟨z2, hz2K, hz2eq⟩ := h2.1
  apply le_antisymm
  · have hz1W : z1 ∈ Wgame V (t • τ) := ⟨z1, hz1K, 0, zero_mem_RtauNonneg _, sub_zero _⟩
    rw [hW.homogeneous t ht τ hτ] at hz1W
    rcases hz1W with ⟨x, hxW, rfl⟩
    rw [← hz1eq]
    have hsum : ∑ i, l i * (t • x) i = t * ∑ i, l i * x i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Pi.smul_apply, smul_eq_mul]; ring
    rw [hsum]
    exact mul_le_mul_of_nonneg_left (h2.2.1 x hxW) ht.le
  · have hz2W : z2 ∈ Wgame V τ := ⟨z2, hz2K, 0, zero_mem_RtauNonneg _, sub_zero _⟩
    have htz2 : t • z2 ∈ Wgame V (t • τ) := by
      rw [hW.homogeneous t ht τ hτ]
      exact ⟨z2, hz2W, rfl⟩
    have hsum : ∑ i, l i * (t • z2) i = t * ∑ i, l i * z2 i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Pi.smul_apply, smul_eq_mul]; ring
    rw [← hz2eq, ← hsum]
    exact h1.2.1 (t • z2) htz2

private lemma wval_continuousOn_l {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hV : IsNTUFuzzyGame V) (h0 : ∀ τ ∈ orthant n, (0 : Fin n → ℝ) ∈ V τ)
    {τ : Fin n → ℝ} (hτ : τ ∈ orthant n) :
    ContinuousOn (fun l => wval V τ l) (orthant n) := by
  obtain ⟨C, _, hC⟩ := hV.bddAbove τ hτ
  have hKbound : ∀ z ∈ Kset V τ, ∀ i, 0 ≤ z i ∧ z i ≤ C i := by
    intro z hz i
    refine ⟨hz.2.2 i, ?_⟩
    rcases hC hz.1 with ⟨c', hc', u, hu, hcu⟩
    rw [mem_singleton_iff] at hc'
    subst hc'
    have h1 := congr_fun hcu i
    simp only [Pi.sub_apply] at h1
    linarith [hu.2 i]
  set L : ℝ := ∑ i : Fin n, C i
  have hL : 0 ≤ L := Finset.sum_nonneg fun i _ => by
    have h := hKbound 0 (zero_mem_Kset h0 hτ) i
    linarith
  have hlip : ∀ l1 ∈ orthant n, ∀ l2 ∈ orthant n,
      |wval V τ l1 - wval V τ l2| ≤ L * ‖l1 - l2‖ := by
    intro l1 hl1 l2 hl2
    obtain ⟨z1, hz1K, hz1eq⟩ := (wval_spec hV h0 hτ hl1).1
    obtain ⟨z2, hz2K, hz2eq⟩ := (wval_spec hV h0 hτ hl2).1
    have hstep : ∀ (a b z : Fin n → ℝ), z ∈ Kset V τ →
        (∑ i, a i * z i) - (∑ i, b i * z i) ≤ L * ‖a - b‖ := by
      intro a b z hz
      calc (∑ i, a i * z i) - (∑ i, b i * z i)
          = ∑ i, (a i - b i) * z i := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun i _ => by ring
        _ ≤ ∑ i, |a i - b i| * z i := by
            refine Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_right (le_abs_self _) (hKbound z hz i).1
        _ ≤ ∑ i, ‖a - b‖ * C i := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hni : |a i - b i| ≤ ‖a - b‖ := by
              simpa [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (a - b) i
            exact mul_le_mul hni (hKbound z hz i).2 (hKbound z hz i).1 (norm_nonneg _)
        _ = L * ‖a - b‖ := by rw [← Finset.mul_sum]; ring
    have hz1W : z1 ∈ Wgame V τ := ⟨z1, hz1K, 0, zero_mem_RtauNonneg _, sub_zero _⟩
    have hz2W : z2 ∈ Wgame V τ := ⟨z2, hz2K, 0, zero_mem_RtauNonneg _, sub_zero _⟩
    have hle1 : wval V τ l1 - wval V τ l2 ≤ L * ‖l1 - l2‖ := by
      have h2 := (wval_spec hV h0 hτ hl2).2.1 z1 hz1W
      linarith [hstep l1 l2 z1 hz1K]
    have hle2 : wval V τ l2 - wval V τ l1 ≤ L * ‖l1 - l2‖ := by
      have h1 := (wval_spec hV h0 hτ hl1).2.1 z2 hz2W
      have hst := hstep l2 l1 z2 hz2K
      rw [norm_sub_rev l2 l1] at hst
      linarith
    exact abs_sub_le_iff.2 ⟨hle1, hle2⟩
  rw [Metric.continuousOn_iff]
  intro l hl ε hε
  refine ⟨ε / (L + 1), div_pos hε (by linarith), fun l' hl' hdist => ?_⟩
  rw [Real.dist_eq]
  rw [dist_eq_norm] at hdist
  calc |wval V τ l' - wval V τ l|
      ≤ L * ‖l' - l‖ := hlip l' hl' l hl
    _ ≤ (L + 1) * ‖l' - l‖ := by nlinarith [norm_nonneg (l' - l)]
    _ < (L + 1) * (ε / (L + 1)) := mul_lt_mul_of_pos_left hdist (by linarith)
    _ = ε := by field_simp [show L + 1 ≠ 0 by linarith]

/-! ### Step 3: Supergradient (TU fuzzy core) existence via Hahn–Banach -/

private lemma exists_tu_core {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hV : IsNTUFuzzyGame V) (hsup : Superadditive V)
    (h0 : ∀ τ ∈ orthant n, (0 : Fin n → ℝ) ∈ V τ)
    {l : Fin n → ℝ} (hlpos : ∀ i, 0 < l i) :
    ∃ c : Fin n → ℝ,
      (∑ i, l i * c i = wval V (coal Finset.univ) l) ∧
      (∀ τ ∈ orthant n, wval V τ l ≤ ∑ i, l i * τ i * c i) := by
  have hl : l ∈ orthant n := fun i => (hlpos i).le
  have hW := Wgame_isNTUFuzzyGame hV h0
  have hWsup := Wgame_superadditive hsup
  have hconc : ConcaveOn ℝ (orthant n) (fun τ => wval V τ l) :=
    (FuzzyGames.NTUCore.support_concave hW hWsup hl).2
  let g : (Fin n → ℝ) → ℝ := fun τ => wval V τ l
  let H : Set ((Fin n → ℝ) × ℝ) := {p | p.1 ∈ orthant n ∧ p.2 ≤ g p.1}
  have hHconv : Convex ℝ H := by
    intro p1 hp1 p2 hp2 a b ha hb hab
    refine ⟨?_, ?_⟩
    · intro i
      exact add_nonneg (mul_nonneg ha (hp1.1 i)) (mul_nonneg hb (hp2.1 i))
    · change a * p1.2 + b * p2.2 ≤ g (a • p1.1 + b • p2.1)
      have h1 : a * p1.2 + b * p2.2 ≤ a * g p1.1 + b * g p2.1 :=
        add_le_add (mul_le_mul_of_nonneg_left hp1.2 ha) (mul_le_mul_of_nonneg_left hp2.2 hb)
      exact h1.trans (hconc.2 hp1.1 hp2.1 ha hb hab)
  have hHint : (interior H).Nonempty := by
    let U : Set ((Fin n → ℝ) × ℝ) := {p | (∀ i, 0 < p.1 i) ∧ p.2 < 0}
    have hUopen : IsOpen U := by
      have h1 : IsOpen {τ : Fin n → ℝ | ∀ i, 0 < τ i} := by
        have : {τ : Fin n → ℝ | ∀ i, 0 < τ i} = ⋂ i : Fin n, {τ : Fin n → ℝ | 0 < τ i} := by
          ext τ; simp
        rw [this]
        exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
      exact (h1.preimage continuous_fst).inter (isOpen_lt continuous_snd continuous_const)
    have hUH : U ⊆ H := by
      intro p hp
      exact ⟨fun i => (hp.1 i).le, hp.2.le.trans (wval_nonneg hV h0 (fun i => (hp.1 i).le) hl)⟩
    refine ⟨(coal Finset.univ, -1), interior_maximal hUH hUopen ?_⟩
    exact ⟨fun i => by simp [coal], by norm_num⟩
  set x0 : (Fin n → ℝ) × ℝ := (coal Finset.univ, g (coal Finset.univ))
  have hx0 : x0 ∉ interior H := by
    intro hmem
    have hnhds : H ∈ nhds x0 := mem_interior_iff_mem_nhds.1 hmem
    have htend : Filter.Tendsto (fun t : ℝ => (coal Finset.univ, g (coal Finset.univ) + t))
        (nhds 0) (nhds x0) := by
      have h2 : Filter.Tendsto (fun t : ℝ => g (coal Finset.univ) + t) (nhds 0)
          (nhds (g (coal Finset.univ) + 0)) := tendsto_const_nhds.add Filter.tendsto_id
      rw [add_zero] at h2
      exact tendsto_const_nhds.prodMk_nhds h2
    have hev : ∀ᶠ t in nhds (0 : ℝ), (coal Finset.univ, g (coal Finset.univ) + t) ∈ H :=
      htend.eventually hnhds
    rcases Metric.eventually_nhds_iff.1 hev with ⟨δ, hδ, hball⟩
    have hmem' := hball (y := δ / 2) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
      linarith)
    have hle : g (coal Finset.univ) + δ / 2 ≤ g (coal Finset.univ) := hmem'.2
    linarith
  obtain ⟨f, hfne, hfmax⟩ := geometric_hahn_banach_of_nonempty_interior_point hHconv hx0 hHint
  set α : ℝ := f (0, 1)
  have hαnonneg : 0 ≤ α := by
    have h1 := hfmax (coal Finset.univ, g (coal Finset.univ) - 1)
      ⟨coal_mem_orthant Finset.univ, by linarith⟩
    have hsplit : (coal Finset.univ, g (coal Finset.univ) - 1) = x0 - (0, 1) := by
      ext <;> simp [x0]
    rw [hsplit, map_sub] at h1
    linarith
  have hαpos : 0 < α := by
    rcases hαnonneg.eq_or_lt with hα0 | hpos
    · exfalso
      have hα0' : f (0, 1) = 0 := hα0.symm
      have hLle : ∀ τ ∈ orthant n, f (τ, 0) ≤ f (coal Finset.univ, 0) := by
        intro τ hτ
        have h1 := hfmax (τ, g τ) ⟨hτ, le_rfl⟩
        have hsplit1 : (τ, g τ) = (τ, 0) + g τ • (0, 1) := by ext <;> simp
        have hsplit2 : x0 = (coal Finset.univ, 0) + g (coal Finset.univ) • (0, 1) := by
          ext <;> simp [x0]
        rw [hsplit1, hsplit2, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
          hα0', mul_zero, mul_zero, add_zero, add_zero] at h1
        exact h1
      have hLzero : ∀ v : Fin n → ℝ, f (v, 0) = 0 := by
        intro v
        let M : ℝ := (∑ i : Fin n, |v i|) + 1
        have hM : 0 < M := by
          have : 0 ≤ ∑ i : Fin n, |v i| := Finset.sum_nonneg fun i _ => abs_nonneg _
          linarith
        have hle_M : ∀ i, |v i| ≤ M := fun i => by
          have : |v i| ≤ ∑ j : Fin n, |v j| :=
            Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)
          linarith
        have hplus : coal Finset.univ + M⁻¹ • v ∈ orthant n := by
          intro i
          simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, coal_univ_apply]
          have h1 : -(M⁻¹ * |v i|) ≤ M⁻¹ * v i := by
            have := neg_abs_le (v i)
            nlinarith [inv_pos.2 hM]
          have h2 : M⁻¹ * |v i| ≤ 1 := by
            rw [inv_mul_le_iff₀ hM]
            linarith [hle_M i]
          linarith
        have hminus : coal Finset.univ + (-M⁻¹) • v ∈ orthant n := by
          intro i
          simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, coal_univ_apply]
          have h1 : -(M⁻¹ * |v i|) ≤ -(M⁻¹ * v i) := by
            have := le_abs_self (v i)
            nlinarith [inv_pos.2 hM]
          have h2 : M⁻¹ * |v i| ≤ 1 := by
            rw [inv_mul_le_iff₀ hM]
            linarith [hle_M i]
          linarith
        have hp1 := hLle _ hplus
        have hm1 := hLle _ hminus
        have hs1 : (coal Finset.univ + M⁻¹ • v, (0 : ℝ)) =
            (coal Finset.univ, 0) + M⁻¹ • (v, 0) := by ext <;> simp
        have hs2 : (coal Finset.univ + (-M⁻¹) • v, (0 : ℝ)) =
            (coal Finset.univ, 0) + (-M⁻¹) • (v, 0) := by ext <;> simp
        rw [hs1, map_add, map_smul, smul_eq_mul] at hp1
        rw [hs2, map_add, map_smul, smul_eq_mul] at hm1
        have hpos_inv : 0 < M⁻¹ := inv_pos.2 hM
        have hle0 : f (v, 0) ≤ 0 := by nlinarith
        have hge0 : 0 ≤ f (v, 0) := by nlinarith
        linarith
      apply hfne
      refine ContinuousLinearMap.ext fun p => ?_
      have hdecomp : p = (p.1, 0) + p.2 • (0, 1) := by ext <;> simp
      rw [hdecomp, map_add, map_smul, smul_eq_mul, hLzero p.1, hα0', mul_zero, add_zero]
      rfl
    · exact hpos
  let p : Fin n → ℝ := fun i => -(f (Pi.single i 1, 0)) / α
  have hf_formula : ∀ τ : Fin n → ℝ, f (τ, 0) = -α * ∑ i, τ i * p i := by
    intro τ
    have hτsum : (τ, (0 : ℝ)) = ∑ i : Fin n, τ i • (Pi.single i 1, (0 : ℝ)) := by
      ext j
      · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
    rw [hτsum, map_sum]
    simp_rw [map_smul, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [p]
    field_simp [hαpos.ne']
  have hineq : ∀ τ ∈ orthant n, g τ - ∑ i, τ i * p i ≤ g (coal Finset.univ) - ∑ i, p i := by
    intro τ hτ
    have h1 := hfmax (τ, g τ) ⟨hτ, le_rfl⟩
    have hsplit1 : (τ, g τ) = (τ, 0) + g τ • (0, 1) := by ext <;> simp
    have hsplit2 : x0 = (coal Finset.univ, 0) + g (coal Finset.univ) • (0, 1) := by
      ext <;> simp [x0]
    rw [hsplit1, hsplit2, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      hf_formula τ, hf_formula (coal Finset.univ)] at h1
    have hsum1 : ∑ i : Fin n, coal (Finset.univ : Finset (Fin n)) i * p i = ∑ i, p i := by
      refine Finset.sum_congr rfl fun i _ => by simp [coal]
    rw [hsum1] at h1
    change -α * ∑ i, τ i * p i + g τ * α ≤ -α * ∑ i, p i + g (coal Finset.univ) * α at h1
    nlinarith
  have hge : ∑ i, p i ≤ g (coal Finset.univ) := by
    have h0' := hineq 0 zero_mem_orthant
    have hg0 : g 0 = 0 := wval_zero hV h0 hl
    simp only [hg0, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_self] at h0'
    linarith
  have hle : g (coal Finset.univ) ≤ ∑ i, p i := by
    have h2mem : (2 : ℝ) • coal (Finset.univ : Finset (Fin n)) ∈ orthant n :=
      fun i => mul_nonneg (by norm_num) (coal_mem_orthant Finset.univ i)
    have h2' := hineq _ h2mem
    have hg2 : g ((2 : ℝ) • coal Finset.univ) = 2 * g (coal Finset.univ) :=
      wval_smul hV h0 (by norm_num) (coal_mem_orthant Finset.univ) hl
    have hsum2 : ∑ i : Fin n, ((2 : ℝ) • coal (Finset.univ : Finset (Fin n))) i * p i =
        2 * ∑ i, p i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by simp [coal]
    rw [hg2, hsum2] at h2'
    linarith
  have heq : ∑ i, p i = g (coal Finset.univ) := le_antisymm hge hle
  refine ⟨fun i => p i / l i, ?_, ?_⟩
  · have : ∑ i, l i * (p i / l i) = ∑ i, p i :=
      Finset.sum_congr rfl fun i _ => mul_div_cancel₀ (p i) (hlpos i).ne'
    rw [this, heq]
  · intro τ hτ
    have h1 := hineq τ hτ
    rw [heq, sub_self] at h1
    have h2 : ∑ i, l i * τ i * (p i / l i) = ∑ i, τ i * p i :=
      Finset.sum_congr rfl fun i _ => by field_simp [(hlpos i).ne']
    rw [h2]
    linarith

/-! ### Step 4: Closed graph implies upper hemicontinuity into a compact domain -/

private lemma upperHemicontinuousOn_of_closed_graph {E : Type*} [TopologicalSpace E] [T2Space E]
    {D : Set E} (hD : IsCompact D) {Φ : E → Set E}
    (hΦD : ∀ x ∈ D, Φ x ⊆ D)
    (hG : IsClosed {p : E × E | p.1 ∈ D ∧ p.2 ∈ D ∧ p.2 ∈ Φ p.1}) :
    UpperHemicontinuousOn Φ D := by
  rw [upperHemicontinuousOn_iff_forall_isOpen]
  intro x hx u hu hΦu
  let F : Set E := D \ u
  have hFcomp : IsCompact F := hD.diff hu
  let GF : Set (E × E) := {p : E × E | p.1 ∈ D ∧ p.2 ∈ D ∧ p.2 ∈ Φ p.1} ∩ (D ×ˢ F)
  have hGFcomp : IsCompact GF := (hD.prod hFcomp).inter_left hG
  let CF : Set E := Prod.fst '' GF
  have hCFclosed : IsClosed CF := (hGFcomp.image continuous_fst).isClosed
  have hxCF : x ∉ CF := by
    rintro ⟨⟨x', y'⟩, ⟨⟨_, _, hy'⟩, ⟨_, _, hy'u⟩⟩, rfl⟩
    exact hy'u (hΦu hy')
  have hnhds : CFᶜ ∈ nhds x := hCFclosed.isOpen_compl.mem_nhds hxCF
  refine Filter.mem_of_superset (Filter.inter_mem (nhdsWithin_le_nhds hnhds) self_mem_nhdsWithin) ?_
  rintro x' ⟨hx'CF, hx'D⟩ y' hy'
  by_contra hy'u
  apply hx'CF
  exact ⟨(x', y'), ⟨⟨hx'D, hΦD x' hx'D hy', hy'⟩, ⟨hx'D, hΦD x' hx'D hy', hy'u⟩⟩, rfl⟩

/-! ### Step 5: Fixed point on `M_ε × B_ε × K` for each `ε ∈ (0, 1/(2n)]` -/

private lemma exists_approx_eq {n : ℕ} (hn : 0 < n) {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hV : IsNTUFuzzyGame V) (hsup : Superadditive V)
    (h0 : ∀ τ ∈ orthant n, (0 : Fin n → ℝ) ∈ V τ)
    (h1 : ∀ i, ∀ c ∈ V (coal {i}), c i ≤ 0)
    {C : Fin n → ℝ} (hC : V (coal Finset.univ) ⊆ {C} - RtauNonneg (coal Finset.univ))
    {ε : ℝ} (hε : 0 < ε) (hεn : (n : ℝ) * ε ≤ 1 / 2) :
    ∃ (l c y : Fin n → ℝ),
      (∀ i, ε ≤ l i) ∧ (∑ i, l i = 1) ∧
      y ∈ Kset V (coal Finset.univ) ∧
      (∀ i, 0 ≤ c i) ∧
      (∀ τ ∈ orthant n, wval V τ l ≤ ∑ i, l i * τ i * c i) ∧
      (∀ i, c i ≤ y i + (ε / (1 - (n : ℝ) * ε)) * ∑ j, C j) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  have hKbound : ∀ y ∈ Kset V (coal Finset.univ), ∀ i, 0 ≤ y i ∧ y i ≤ C i := by
    intro y hy i
    refine ⟨hy.2.2 i, ?_⟩
    rcases hC hy.1 with ⟨c', hc', u, hu, hcu⟩
    rw [mem_singleton_iff] at hc'
    subst hc'
    have h1' := congr_fun hcu i
    simp only [Pi.sub_apply] at h1'
    linarith [hu.2 i]
  set MC : ℝ := ∑ j : Fin n, C j
  have hMC : 0 ≤ MC := Finset.sum_nonneg fun i _ => by
    have := hKbound 0 (zero_mem_Kset h0 (coal_mem_orthant Finset.univ)) i
    linarith
  let Meps : Set (Fin n → ℝ) := {l | (∀ i, ε ≤ l i) ∧ ∑ i, l i = 1}
  let Beps : Set (Fin n → ℝ) := {c | ∀ i, 0 ≤ c i ∧ c i ≤ MC / ε}
  let K : Set (Fin n → ℝ) := Kset V (coal Finset.univ)
  have hMeps_sub : Meps ⊆ Set.Icc 0 1 := by
    intro l hl
    refine ⟨fun i => hε.le.trans (hl.1 i), fun i => ?_⟩
    have hle : l i ≤ ∑ j : Fin n, l j :=
      Finset.single_le_sum (fun j _ => hε.le.trans (hl.1 j)) (Finset.mem_univ i)
    simp only [Pi.one_apply]
    linarith [hl.2]
  have hMeps_closed : IsClosed Meps := by
    have h1' : IsClosed {l : Fin n → ℝ | ∀ i, ε ≤ l i} := by
      have : {l : Fin n → ℝ | ∀ i, ε ≤ l i} = ⋂ i : Fin n, {l : Fin n → ℝ | ε ≤ l i} := by
        ext l; simp
      rw [this]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2' : IsClosed {l : Fin n → ℝ | ∑ i, l i = 1} :=
      isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    exact h1'.inter h2'
  have hMeps_comp : IsCompact Meps := isCompact_Icc.of_isClosed_subset hMeps_closed hMeps_sub
  have hMeps_ne : Meps.Nonempty := by
    refine ⟨fun _ => 1 / (n : ℝ), fun i => ?_, ?_⟩
    · rw [le_div_iff₀ hn_pos]
      linarith
    · simp [hn_pos.ne']
  have hMeps_conv : Convex ℝ Meps := by
    intro l1 hl1 l2 hl2 a b ha hb hab
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc ε = (a + b) * ε := by rw [hab, one_mul]
        _ = a * ε + b * ε := by ring
        _ ≤ a * l1 i + b * l2 i :=
            add_le_add (mul_le_mul_of_nonneg_left (hl1.1 i) ha)
              (mul_le_mul_of_nonneg_left (hl2.1 i) hb)
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hl1.2, hl2.2, mul_one, hab]
  have hBeps_eq : Beps = Set.Icc (0 : Fin n → ℝ) (fun _ => MC / ε) := by
    ext c
    simp only [Beps, mem_ofPred_eq, Set.mem_Icc]
    exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun ⟨h1, h2⟩ i => ⟨h1 i, h2 i⟩⟩
  have hBeps_comp : IsCompact Beps := by rw [hBeps_eq]; exact isCompact_Icc
  have hBeps_ne : Beps.Nonempty := ⟨0, fun _ => ⟨le_rfl, div_nonneg hMC hε.le⟩⟩
  have hBeps_conv : Convex ℝ Beps := by rw [hBeps_eq]; exact convex_Icc _ _
  have hK_comp : IsCompact K := Kset_isCompact hV (coal_mem_orthant Finset.univ)
  have hK_ne : K.Nonempty := ⟨0, zero_mem_Kset h0 (coal_mem_orthant Finset.univ)⟩
  have hK_conv : Convex ℝ K := Kset_convex hV (coal_mem_orthant Finset.univ)
  -- Product domain D in E
  let D : Set ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) := Meps ×ˢ (Beps ×ˢ K)
  have hD_ne : D.Nonempty := hMeps_ne.prod (hBeps_ne.prod hK_ne)
  have hD_comp : IsCompact D := hMeps_comp.prod (hBeps_comp.prod hK_comp)
  have hD_conv : Convex ℝ D := hMeps_conv.prod (hBeps_conv.prod hK_conv)
  -- Correspondence components
  let A1 : (Fin n → ℝ) → (Fin n → ℝ) → Set (Fin n → ℝ) := fun c y =>
    {μ ∈ Meps | ∀ μ' ∈ Meps, ∑ i, μ' i * (c i - y i) ≤ ∑ i, μ i * (c i - y i)}
  let A2 : (Fin n → ℝ) → Set (Fin n → ℝ) := fun l =>
    {c' ∈ Beps | ∑ i, l i * c' i = wval V (coal Finset.univ) l ∧
      ∀ τ ∈ orthant n, wval V τ l ≤ ∑ i, l i * τ i * c' i}
  let A3 : (Fin n → ℝ) → Set (Fin n → ℝ) := fun l =>
    {y' ∈ K | ∀ y ∈ K, ∑ i, l i * y i ≤ ∑ i, l i * y' i}
  let Φ : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) →
      Set ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) :=
    fun x => A1 x.2.1 x.2.2 ×ˢ (A2 x.1 ×ˢ A3 x.1)
  have hΦD : ∀ x ∈ D, Φ x ⊆ D := by
    rintro ⟨l, c, y⟩ _ ⟨l', c', y'⟩ ⟨hl', hc', hy'⟩
    exact ⟨hl'.1, hc'.1, hy'.1⟩
  have hA1_ne : ∀ c y, (A1 c y).Nonempty := by
    intro c y
    have hcont : Continuous (fun μ : Fin n → ℝ => ∑ i, μ i * (c i - y i)) :=
      continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const
    obtain ⟨μ, hμ, hmax⟩ := hMeps_comp.exists_isMaxOn hMeps_ne hcont.continuousOn
    exact ⟨μ, hμ, fun μ' hμ' => hmax hμ'⟩
  have hA2_ne : ∀ l ∈ Meps, (A2 l).Nonempty := by
    intro l hl
    have hlpos : ∀ i, 0 < l i := fun i => hε.trans_le (hl.1 i)
    have hlorth : l ∈ orthant n := fun i => (hlpos i).le
    obtain ⟨c', hc'eq, hc'ge⟩ := exists_tu_core hV hsup h0 hlpos
    have hc'B : c' ∈ Beps := by
      intro i
      have hci0 : 0 ≤ c' i := by
        have hsing := hc'ge (coal {i}) (coal_mem_orthant {i})
        rw [wval_singleton hV h0 h1 i hlorth] at hsing
        have hsum : ∑ j : Fin n, l j * coal ({i} : Finset (Fin n)) j * c' j = l i * c' i := by
          rw [Finset.sum_eq_single i]
          · simp [coal]
          · intro j _ hji; simp [coal, hji]
          · intro hi; exact absurd (Finset.mem_univ i) hi
        rw [hsum] at hsing
        exact nonneg_of_mul_nonneg_right hsing (hlpos i)
      refine ⟨hci0, ?_⟩
      rw [le_div_iff₀ hε]
      have hterm : c' i * ε ≤ l i * c' i := by nlinarith [hl.1 i]
      have hsumle : l i * c' i ≤ ∑ j, l j * c' j :=
        Finset.single_le_sum (fun j _ => by
          have hsing := hc'ge (coal {j}) (coal_mem_orthant {j})
          rw [wval_singleton hV h0 h1 j hlorth] at hsing
          have hsum' : ∑ k : Fin n, l k * coal ({j} : Finset (Fin n)) k * c' k = l j * c' j := by
            rw [Finset.sum_eq_single j]
            · simp [coal]
            · intro k _ hkj; simp [coal, hkj]
            · intro hj; exact absurd (Finset.mem_univ j) hj
          rwa [hsum'] at hsing) (Finset.mem_univ i)
      obtain ⟨z, hzK, hzeq⟩ := (wval_spec hV h0 (coal_mem_orthant Finset.univ) hlorth).1
      have hwle : wval V (coal Finset.univ) l ≤ MC := by
        rw [← hzeq]
        refine Finset.sum_le_sum fun j _ => ?_
        have hlj1 : l j ≤ 1 := (hMeps_sub hl).2 j
        have hzj := hKbound z hzK j
        calc l j * z j ≤ 1 * C j :=
              mul_le_mul hlj1 hzj.2 hzj.1 (by norm_num)
          _ = C j := one_mul _
      linarith
    exact ⟨c', hc'B, hc'eq, hc'ge⟩
  have hA3_ne : ∀ l, (A3 l).Nonempty := by
    intro l
    have hcont : Continuous (fun y : Fin n → ℝ => ∑ i, l i * y i) :=
      continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)
    obtain ⟨y', hy', hmax⟩ := hK_comp.exists_isMaxOn hK_ne hcont.continuousOn
    exact ⟨y', hy', fun y hy => hmax hy⟩
  have hΦne : ∀ x ∈ D, (Φ x).Nonempty := by
    rintro ⟨l, c, y⟩ ⟨hl, _, _⟩
    exact (hA1_ne c y).prod ((hA2_ne l hl).prod (hA3_ne l))
  have hΦconv : ∀ x ∈ D, Convex ℝ (Φ x) := by
    rintro ⟨l, c, y⟩ _
    refine Convex.prod ?_ (Convex.prod ?_ ?_)
    · intro μ1 hμ1 μ2 hμ2 a b ha hb hab
      refine ⟨hMeps_conv hμ1.1 hμ2.1 ha hb hab, fun μ' hμ' => ?_⟩
      have hlin : ∑ i, (a • μ1 + b • μ2) i * (c i - y i) =
          a * (∑ i, μ1 i * (c i - y i)) + b * (∑ i, μ2 i * (c i - y i)) := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
          mul_assoc, ← Finset.mul_sum]
      rw [hlin]
      calc ∑ i, μ' i * (c i - y i)
          = (a + b) * ∑ i, μ' i * (c i - y i) := by rw [hab, one_mul]
        _ = a * ∑ i, μ' i * (c i - y i) + b * ∑ i, μ' i * (c i - y i) := by ring
        _ ≤ a * ∑ i, μ1 i * (c i - y i) + b * ∑ i, μ2 i * (c i - y i) :=
            add_le_add (mul_le_mul_of_nonneg_left (hμ1.2 μ' hμ') ha)
              (mul_le_mul_of_nonneg_left (hμ2.2 μ' hμ') hb)
    · intro c1 hc1 c2 hc2 a b ha hb hab
      refine ⟨hBeps_conv hc1.1 hc2.1 ha hb hab, ?_, fun τ hτ => ?_⟩
      · have hlin : ∑ i, l i * (a • c1 + b • c2) i =
            a * (∑ i, l i * c1 i) + b * (∑ i, l i * c2 i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
          congr 1 <;> (rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring)
        change ∑ i, l i * (a • c1 + b • c2) i = wval V (coal Finset.univ) l
        rw [hlin, hc1.2.1, hc2.2.1]
        calc a * wval V (coal Finset.univ) l + b * wval V (coal Finset.univ) l
            = (a + b) * wval V (coal Finset.univ) l := by ring
          _ = wval V (coal Finset.univ) l := by rw [hab, one_mul]
      · have hlin : ∑ i, l i * τ i * (a • c1 + b • c2) i =
            a * (∑ i, l i * τ i * c1 i) + b * (∑ i, l i * τ i * c2 i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
          congr 1 <;> (rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring)
        rw [hlin]
        calc wval V τ l = (a + b) * wval V τ l := by rw [hab, one_mul]
          _ = a * wval V τ l + b * wval V τ l := by ring
          _ ≤ a * ∑ i, l i * τ i * c1 i + b * ∑ i, l i * τ i * c2 i :=
              add_le_add (mul_le_mul_of_nonneg_left (hc1.2.2 τ hτ) ha)
                (mul_le_mul_of_nonneg_left (hc2.2.2 τ hτ) hb)
    · intro y1 hy1 y2 hy2 a b ha hb hab
      refine ⟨hK_conv hy1.1 hy2.1 ha hb hab, fun y' hy' => ?_⟩
      have hlin : ∑ i, l i * (a • y1 + b • y2) i =
          a * (∑ i, l i * y1 i) + b * (∑ i, l i * y2 i) := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
        congr 1 <;> (rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring)
      rw [hlin]
      calc ∑ i, l i * y' i = (a + b) * ∑ i, l i * y' i := by rw [hab, one_mul]
        _ = a * ∑ i, l i * y' i + b * ∑ i, l i * y' i := by ring
        _ ≤ a * ∑ i, l i * y1 i + b * ∑ i, l i * y2 i :=
            add_le_add (mul_le_mul_of_nonneg_left (hy1.2 y' hy') ha)
              (mul_le_mul_of_nonneg_left (hy2.2 y' hy') hb)
  -- Closed graph of Φ on D × D
  have hGclosed : IsClosed {p : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) ×
      ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) |
      p.1 ∈ D ∧ p.2 ∈ D ∧ p.2 ∈ Φ p.1} := by
    have hDclosed : IsClosed D := hD_comp.isClosed
    -- Write the graph as an intersection of closed sets
    have hMeps_orth : Meps ⊆ orthant n := fun l hl i => hε.le.trans (hl.1 i)
    -- Wait: check closedness directly via `isClosed_iff_forall_filter` / sequences!
    rw [← isSeqClosed_iff_isClosed]
    intro u z hu hz
    have hz1 : Filter.Tendsto (fun m => (u m).1) Filter.atTop (nhds z.1) :=
      continuous_fst.continuousAt.tendsto.comp hz
    have hz2 : Filter.Tendsto (fun m => (u m).2) Filter.atTop (nhds z.2) :=
      continuous_snd.continuousAt.tendsto.comp hz
    have hz11 : Filter.Tendsto (fun m => (u m).1.1) Filter.atTop (nhds z.1.1) :=
      continuous_fst.continuousAt.tendsto.comp hz1
    have hz121 : Filter.Tendsto (fun m => (u m).1.2.1) Filter.atTop (nhds z.1.2.1) :=
      (continuous_fst.comp continuous_snd).continuousAt.tendsto.comp hz1
    have hz122 : Filter.Tendsto (fun m => (u m).1.2.2) Filter.atTop (nhds z.1.2.2) :=
      (continuous_snd.comp continuous_snd).continuousAt.tendsto.comp hz1
    have hz21 : Filter.Tendsto (fun m => (u m).2.1) Filter.atTop (nhds z.2.1) :=
      continuous_fst.continuousAt.tendsto.comp hz2
    have hz221 : Filter.Tendsto (fun m => (u m).2.2.1) Filter.atTop (nhds z.2.2.1) :=
      (continuous_fst.comp continuous_snd).continuousAt.tendsto.comp hz2
    have hz222 : Filter.Tendsto (fun m => (u m).2.2.2) Filter.atTop (nhds z.2.2.2) :=
      (continuous_snd.comp continuous_snd).continuousAt.tendsto.comp hz2
    have h1D : z.1 ∈ D := hDclosed.mem_of_tendsto hz1 (Filter.Eventually.of_forall fun m => (hu m).1)
    have h2D : z.2 ∈ D := hDclosed.mem_of_tendsto hz2 (Filter.Eventually.of_forall fun m => (hu m).2.1)
    refine ⟨h1D, h2D, ?_, ?_, ?_⟩
    · -- z.2.1 ∈ A1 z.1.2.1 z.1.2.2
      refine ⟨h2D.1, fun μ' hμ' => ?_⟩
      have hlim1 : Filter.Tendsto (fun m => ∑ i, μ' i * ((u m).1.2.1 i - (u m).1.2.2 i))
          Filter.atTop (nhds (∑ i, μ' i * (z.1.2.1 i - z.1.2.2 i))) :=
        tendsto_finsetSum _ fun i _ => tendsto_const_nhds.mul
          (((continuous_apply i).continuousAt.tendsto.comp hz121).sub
            ((continuous_apply i).continuousAt.tendsto.comp hz122))
      have hlim2 : Filter.Tendsto (fun m => ∑ i, (u m).2.1 i * ((u m).1.2.1 i - (u m).1.2.2 i))
          Filter.atTop (nhds (∑ i, z.2.1 i * (z.1.2.1 i - z.1.2.2 i))) :=
        tendsto_finsetSum _ fun i _ =>
          ((continuous_apply i).continuousAt.tendsto.comp hz21).mul
            (((continuous_apply i).continuousAt.tendsto.comp hz121).sub
              ((continuous_apply i).continuousAt.tendsto.comp hz122))
      exact le_of_tendsto_of_tendsto hlim1 hlim2
        (Filter.Eventually.of_forall fun m => (hu m).2.2.1.2 μ' hμ')
    · -- z.2.2.1 ∈ A2 z.1.1
      refine ⟨h2D.2.1, ?_, fun τ hτ => ?_⟩
      · have hlimL : Filter.Tendsto (fun m => ∑ i, (u m).1.1 i * (u m).2.2.1 i)
            Filter.atTop (nhds (∑ i, z.1.1 i * z.2.2.1 i)) :=
          tendsto_finsetSum _ fun i _ =>
            ((continuous_apply i).continuousAt.tendsto.comp hz11).mul
              ((continuous_apply i).continuousAt.tendsto.comp hz221)
        have hlimR : Filter.Tendsto (fun m => wval V (coal Finset.univ) (u m).1.1)
            Filter.atTop (nhds (wval V (coal Finset.univ) z.1.1)) := by
          have hcont := (wval_continuousOn_l hV h0 (coal_mem_orthant Finset.univ)).continuousWithinAt
            (hMeps_orth h1D.1)
          exact hcont.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            hz11 (Filter.Eventually.of_forall fun m => hMeps_orth (hu m).1.1))
        exact tendsto_nhds_unique hlimL (hlimR.congr fun m => ((hu m).2.2.2.1.2.1).symm)
      · have hlimL : Filter.Tendsto (fun m => wval V τ (u m).1.1)
            Filter.atTop (nhds (wval V τ z.1.1)) := by
          have hcont := (wval_continuousOn_l hV h0 hτ).continuousWithinAt (hMeps_orth h1D.1)
          exact hcont.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            hz11 (Filter.Eventually.of_forall fun m => hMeps_orth (hu m).1.1))
        have hlimR : Filter.Tendsto (fun m => ∑ i, (u m).1.1 i * τ i * (u m).2.2.1 i)
            Filter.atTop (nhds (∑ i, z.1.1 i * τ i * z.2.2.1 i)) :=
          tendsto_finsetSum _ fun i _ =>
            (((continuous_apply i).continuousAt.tendsto.comp hz11).mul tendsto_const_nhds).mul
              ((continuous_apply i).continuousAt.tendsto.comp hz221)
        exact le_of_tendsto_of_tendsto hlimL hlimR
          (Filter.Eventually.of_forall fun m => (hu m).2.2.2.1.2.2 τ hτ)
    · -- z.2.2.2 ∈ A3 z.1.1
      refine ⟨h2D.2.2, fun y' hy' => ?_⟩
      have hlimL : Filter.Tendsto (fun m => ∑ i, (u m).1.1 i * y' i)
          Filter.atTop (nhds (∑ i, z.1.1 i * y' i)) :=
        tendsto_finsetSum _ fun i _ =>
          ((continuous_apply i).continuousAt.tendsto.comp hz11).mul tendsto_const_nhds
      have hlimR : Filter.Tendsto (fun m => ∑ i, (u m).1.1 i * (u m).2.2.2 i)
          Filter.atTop (nhds (∑ i, z.1.1 i * z.2.2.2 i)) :=
        tendsto_finsetSum _ fun i _ =>
          ((continuous_apply i).continuousAt.tendsto.comp hz11).mul
            ((continuous_apply i).continuousAt.tendsto.comp hz222)
      exact le_of_tendsto_of_tendsto hlimL hlimR
        (Filter.Eventually.of_forall fun m => (hu m).2.2.2.2.2 y' hy')
  have hΦclosed : ∀ x ∈ D, IsClosed (Φ x) := by
    intro x hx
    have hpre : Φ x = (fun y => (x, y)) ⁻¹'
        {p | p.1 ∈ D ∧ p.2 ∈ D ∧ p.2 ∈ Φ p.1} := by
      ext y
      simp only [Set.mem_preimage, mem_ofPred_eq]
      exact ⟨fun hy => ⟨hx, hΦD x hx hy, hy⟩, fun h => h.2.2⟩
    rw [hpre]
    exact hGclosed.preimage (continuous_const.prodMk continuous_id)
  have hΦuhc : UpperHemicontinuousOn Φ D :=
    upperHemicontinuousOn_of_closed_graph hD_comp hΦD hGclosed
  obtain ⟨⟨l, c, y⟩, ⟨hl, hcB, hyK⟩, hfix⟩ :=
    FanGlicksberg.kakutani_fan_glicksberg D hD_ne hD_comp hD_conv Φ hΦuhc hΦD hΦne hΦconv hΦclosed
  rcases hfix with ⟨⟨_, hmaxμ⟩, ⟨_, hceq, hcge⟩, ⟨_, hmaxy⟩⟩
  have hlorth : l ∈ orthant n := fun i => hε.le.trans (hl.1 i)
  have hyeq : ∑ i, l i * y i = wval V (coal Finset.univ) l := by
    obtain ⟨z0, hz0K, hz0eq⟩ := (wval_spec hV h0 (coal_mem_orthant Finset.univ) hlorth).1
    apply le_antisymm
    · exact (wval_spec hV h0 (coal_mem_orthant Finset.univ) hlorth).2.1 y
        ⟨y, hyK, 0, zero_mem_RtauNonneg _, sub_zero _⟩
    · rw [← hz0eq]
      exact hmaxy z0 hz0K
  have hdot0 : ∑ i, l i * (c i - y i) = 0 := by
    have : ∑ i, l i * (c i - y i) = (∑ i, l i * c i) - ∑ i, l i * y i := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [this, hceq, hyeq, sub_self]
  refine ⟨l, c, y, hl.1, hl.2, hyK, fun i => (hcB i).1, hcge, fun i => ?_⟩
  let μ : Fin n → ℝ := fun j => (1 - (n : ℝ) * ε) * coal {i} j + ε
  have hμM : μ ∈ Meps := by
    refine ⟨fun j => ?_, ?_⟩
    · have h1' : 0 ≤ (1 - (n : ℝ) * ε) * coal {i} j :=
        mul_nonneg (by linarith) (coal_mem_orthant {i} j)
      dsimp [μ]; linarith
    · simp only [μ, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hsc : ∑ j : Fin n, coal ({i} : Finset (Fin n)) j = 1 := by
        rw [Finset.sum_eq_single i]
        · simp [coal]
        · intro j _ hji; simp [coal, hji]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      rw [hsc]; ring
  have hμle : ∑ j, μ j * (c j - y j) ≤ 0 := by
    simpa only [hdot0] using hmaxμ μ hμM
  have hexpand : ∑ j, μ j * (c j - y j) =
      (1 - (n : ℝ) * ε) * (c i - y i) + ε * ∑ j, c j - ε * ∑ j, y j := by
    have h1' : ∑ j, μ j * (c j - y j) =
        (∑ j, (1 - (n : ℝ) * ε) * coal {i} j * (c j - y j)) +
        (∑ j, ε * c j) - (∑ j, ε * y j) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => by dsimp [μ]; ring
    rw [h1', ← Finset.mul_sum, ← Finset.mul_sum]
    congr 2
    rw [Finset.sum_eq_single i]
    · simp [coal]
    · intro j _ hji; simp [coal, hji]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [hexpand] at hμle
  have hsumc : 0 ≤ ∑ j, c j := Finset.sum_nonneg fun j _ => (hcB j).1
  have hsumy : ∑ j, y j ≤ MC := Finset.sum_le_sum fun j _ => (hKbound y hyK j).2
  have h1m : 0 < 1 - (n : ℝ) * ε := by linarith
  have hineq1 : (1 - (n : ℝ) * ε) * (c i - y i) ≤ ε * MC := by nlinarith
  have hineq2 : c i - y i ≤ (ε / (1 - (n : ℝ) * ε)) * MC := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h1m]
    linarith
  linarith

/-! ### Step 6: Limit as `ε → 0` yields a core point of a normalized game -/

private lemma exists_core_normalized {n : ℕ} (hn : 0 < n) {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hV : IsNTUFuzzyGame V) (hsup : Superadditive V)
    (h0 : ∀ τ ∈ orthant n, (0 : Fin n → ℝ) ∈ V τ)
    (h1 : ∀ i, ∀ c ∈ V (coal {i}), c i ≤ 0) :
    (fuzzyCore V).Nonempty := by
  obtain ⟨C, _, hC⟩ := hV.bddAbove (coal Finset.univ) (coal_mem_orthant Finset.univ)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  have hKbound : ∀ y ∈ Kset V (coal Finset.univ), ∀ i, 0 ≤ y i ∧ y i ≤ C i := by
    intro y hy i
    refine ⟨hy.2.2 i, ?_⟩
    rcases hC hy.1 with ⟨c', hc', u, hu, hcu⟩
    rw [mem_singleton_iff] at hc'
    subst hc'
    have h1' := congr_fun hcu i
    simp only [Pi.sub_apply] at h1'
    linarith [hu.2 i]
  set MC : ℝ := ∑ j : Fin n, C j
  have hMC : 0 ≤ MC := Finset.sum_nonneg fun i _ => by
    have := hKbound 0 (zero_mem_Kset h0 (coal_mem_orthant Finset.univ)) i
    linarith
  let eps : ℕ → ℝ := fun k => 1 / ((n : ℝ) * ((k : ℝ) + 2))
  have heps_pos : ∀ k, 0 < eps k := fun k => by
    dsimp [eps]; positivity
  have heps_le : ∀ k, (n : ℝ) * eps k ≤ 1 / 2 := fun k => by
    dsimp [eps]
    have hk : (2 : ℝ) ≤ (k : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hne : (n : ℝ) * ((k : ℝ) + 2) ≠ 0 := by positivity
    have h1' : (n : ℝ) * (1 / ((n : ℝ) * ((k : ℝ) + 2))) = 1 / ((k : ℝ) + 2) := by
      field_simp [hn_pos.ne']
    rw [h1']
    exact one_div_le_one_div_of_le (by norm_num) hk
  have hseq : ∀ k : ℕ, ∃ (l c y : Fin n → ℝ),
      (∀ i, eps k ≤ l i) ∧ (∑ i, l i = 1) ∧
      y ∈ Kset V (coal Finset.univ) ∧
      (∀ i, 0 ≤ c i) ∧
      (∀ τ ∈ orthant n, wval V τ l ≤ ∑ i, l i * τ i * c i) ∧
      (∀ i, c i ≤ y i + (eps k / (1 - (n : ℝ) * eps k)) * MC) :=
    fun k => exists_approx_eq hn hV hsup h0 h1 hC (heps_pos k) (heps_le k)
  choose l c y hlpos hlsum hyK hc0 hcge hcle using hseq
  have hratio : ∀ k : ℕ, eps k / (1 - (n : ℝ) * eps k) ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hne1 : 1 - (n : ℝ) * eps k = ((k : ℝ) + 1) / ((k : ℝ) + 2) := by
      dsimp [eps]
      field_simp [hn_pos.ne', hk2.ne']
      ring
    rw [hne1]
    dsimp [eps]
    have hcalc : (1 / ((n : ℝ) * ((k : ℝ) + 2))) / (((k : ℝ) + 1) / ((k : ℝ) + 2)) =
        1 / ((n : ℝ) * ((k : ℝ) + 1)) := by
      field_simp [hn_pos.ne', hk1.ne', hk2.ne']
    rw [hcalc]
    have h1le : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact one_div_le_one_div_of_le hk1 (by nlinarith)
  -- Compact box for (c k, y k)
  let B0 : Set (Fin n → ℝ) := Set.Icc 0 (fun i => C i + MC)
  have hpair_mem : ∀ k : ℕ, (c k, y k) ∈ B0 ×ˢ Kset V (coal Finset.univ) := by
    intro k
    refine ⟨⟨fun i => hc0 k i, fun i => ?_⟩, hyK k⟩
    have h1' := hcle k i
    have h2' := (hKbound (y k) (hyK k) i).2
    have h3' : eps k / (1 - (n : ℝ) * eps k) ≤ 1 :=
      (hratio k).trans (div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity))
    nlinarith
  have hcomp : IsCompact (B0 ×ˢ Kset V (coal Finset.univ)) :=
    isCompact_Icc.prod (Kset_isCompact hV (coal_mem_orthant Finset.univ))
  obtain ⟨⟨cstar, ystar⟩, ⟨hcstarB, hystarK⟩, φ, hφ, htend⟩ := hcomp.tendsto_subseq hpair_mem
  have hc_tend : Filter.Tendsto (fun m => c (φ m)) Filter.atTop (nhds cstar) :=
    continuous_fst.continuousAt.tendsto.comp htend
  have hy_tend : Filter.Tendsto (fun m => y (φ m)) Filter.atTop (nhds ystar) :=
    continuous_snd.continuousAt.tendsto.comp htend
  have hcle_star : ∀ i, cstar i ≤ ystar i := by
    intro i
    have hlimL : Filter.Tendsto (fun m => c (φ m) i) Filter.atTop (nhds (cstar i)) :=
      (continuous_apply i).continuousAt.tendsto.comp hc_tend
    have hlimErr : Filter.Tendsto (fun m => (1 / (((φ m : ℕ) : ℝ) + 1)) * MC)
        Filter.atTop (nhds (0 * MC)) := by
      have hnat : Filter.Tendsto (fun m => (((φ m : ℕ) : ℝ) + 1)) Filter.atTop Filter.atTop :=
        (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop).atTop_add tendsto_const_nhds
      exact (tendsto_const_nhds.div_atTop hnat).mul tendsto_const_nhds
    rw [zero_mul] at hlimErr
    have hlimR : Filter.Tendsto (fun m => y (φ m) i + (1 / (((φ m : ℕ) : ℝ) + 1)) * MC)
        Filter.atTop (nhds (ystar i + 0)) :=
      ((continuous_apply i).continuousAt.tendsto.comp hy_tend).add hlimErr
    rw [add_zero] at hlimR
    exact le_of_tendsto_of_tendsto hlimL hlimR (Filter.Eventually.of_forall fun m => by
      have h1' := hcle (φ m) i
      have h2' := hratio (φ m)
      nlinarith)
  -- cstar ∈ V (coal univ) by comprehensiveness
  have hcstarV : cstar ∈ V (coal Finset.univ) := by
    rw [← hV.comprehensive (coal Finset.univ) (coal_mem_orthant Finset.univ)]
    refine ⟨ystar, hystarK.1, ystar - cstar, ⟨fun i hi => by simp [coal] at hi,
      fun i => sub_nonneg.2 (hcle_star i)⟩, ?_⟩
    ext i; simp
  refine ⟨cstar, hcstarV, ?_⟩
  intro τ hτcube hτne hmem
  have hτorth : τ ∈ orthant n := fun i => hτcube.1 i
  rcases hmem with ⟨z, hzV, u, hu, hzu⟩
  -- Show z ∈ Kset V τ ⊆ Wgame V τ
  have hzK : z ∈ Kset V τ := by
    refine ⟨hzV, hV.subset_Rtau τ hτorth hzV, fun i => ?_⟩
    have hτi0 : (0 : ℝ) ≤ τ i := hτorth i
    rcases hτi0.eq_or_lt with hτ0 | hτpos
    · rw [hV.subset_Rtau τ hτorth hzV i hτ0.symm]
    · have h1' := congr_fun hzu i
      simp only [Pi.sub_apply, tmul] at h1'
      have hui : 0 < u i := hu.2 i hτpos
      have hci : 0 ≤ cstar i := hcstarB.1 i
      nlinarith
  have hzW : z ∈ Wgame V τ := ⟨z, hzK, 0, zero_mem_RtauNonneg τ, sub_zero z⟩
  -- Pick i0 with τ i0 > 0
  have hex_pos : ∃ i0 : Fin n, 0 < τ i0 := by
    by_contra hall
    push Not at hall
    apply hτne
    ext i
    exact le_antisymm (hall i) (hτorth i)
  obtain ⟨i0, hi0⟩ := hex_pos
  -- For large m, for every i with τ i > 0, τ i * c (φ m) i < z i
  have hev_all : ∀ᶠ m in Filter.atTop, ∀ i : Fin n, 0 < τ i → τ i * c (φ m) i < z i := by
    rw [Filter.eventually_all]
    intro i
    by_cases hτi : 0 < τ i
    · have hlim : Filter.Tendsto (fun m => τ i * c (φ m) i) Filter.atTop (nhds (τ i * cstar i)) :=
        tendsto_const_nhds.mul ((continuous_apply i).continuousAt.tendsto.comp hc_tend)
      have hlt : τ i * cstar i < z i := by
        have h1' := congr_fun hzu i
        simp only [Pi.sub_apply, tmul] at h1'
        linarith [hu.2 i hτi]
      exact (hlim.eventually (gt_mem_nhds hlt)).mono fun m hm _ => hm
    · exact Filter.Eventually.of_forall fun _ h => absurd h hτi
  obtain ⟨m, hm⟩ := hev_all.exists
  have hlorth_m : l (φ m) ∈ orthant n := fun i => (heps_pos (φ m)).le.trans (hlpos (φ m) i)
  have hlpos_m : ∀ i, 0 < l (φ m) i := fun i => (heps_pos (φ m)).trans_le (hlpos (φ m) i)
  have hstrict : ∑ i, l (φ m) i * τ i * c (φ m) i < ∑ i, l (φ m) i * z i := by
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i0, Finset.mem_univ i0, ?_⟩
    · have hτi0 : (0 : ℝ) ≤ τ i := hτorth i
      rcases hτi0.eq_or_lt with hτ0 | hτi
      · have hzi0 : z i = 0 := hzK.2.1 i hτ0.symm
        simp [← hτ0, hzi0]
      · have h1' := hm i hτi
        nlinarith [hlpos_m i]
    · have h1' := hm i0 hi0
      nlinarith [hlpos_m i0]
  have hwle : ∑ i, l (φ m) i * z i ≤ wval V τ (l (φ m)) :=
    (wval_spec hV h0 hτorth hlorth_m).2.1 z hzW
  have hcge_m : wval V τ (l (φ m)) ≤ ∑ i, l (φ m) i * τ i * c (φ m) i :=
    hcge (φ m) τ hτorth
  linarith

/-! ### Main theorem -/

theorem solution {n : ℕ} (hn : 0 < n) {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hV : IsNTUFuzzyGame V) (hsup : Superadditive V) :
    (fuzzyCore V).Nonempty ∧ (weakCCE V).Nonempty := by
  have hsing : ∀ i : Fin n, ∃ a : ℝ, Pi.single i a ∈ V (coal {i}) ∧ ∀ c ∈ V (coal {i}), c i ≤ a :=
    fun i => exists_singleton_max hV i
  choose a ha_mem ha_max using hsing
  let V1 := shiftGame V a
  have hV1 : IsNTUFuzzyGame V1 := shiftGame_isNTUFuzzyGame hV hsup ha_mem
  have hsup1 : Superadditive V1 := shiftGame_superadditive hsup a
  have h01 : ∀ τ ∈ orthant n, (0 : Fin n → ℝ) ∈ V1 τ := by
    intro τ hτ
    change 0 + tmul τ a ∈ V τ
    rw [zero_add]
    exact tmul_a_mem hV hsup ha_mem hτ
  have h11 : ∀ i, ∀ c ∈ V1 (coal {i}), c i ≤ 0 := by
    intro i c hc
    have h := ha_max i (c + tmul (coal {i}) a) hc
    simp only [Pi.add_apply, tmul, coal_singleton_apply, if_true, one_mul] at h
    linarith
  obtain ⟨c1, hc1⟩ := exists_core_normalized hn hV1 hsup1 h01 h11
  have hcore : (fuzzyCore V).Nonempty := ⟨c1 + a, shiftGame_core_add hc1⟩
  obtain ⟨c, hc⟩ := hcore
  exact ⟨⟨c, hc⟩, ⟨c, (FuzzyGames.NTUCore.theorem_3_1 hV).2 hsup hn hc⟩⟩
