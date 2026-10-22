-- Prove2me | solution 1 for FastCLO.ETO.implication_display
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:09:56.474436+00:00
-- url     : https://prove2.me/submissions/210a4473-01e3-4fc5-8a0f-a34f97c16a53

import Mathlib
import Definitions.Def_FastCLO_ETO_Model

set_option autoImplicit false
open scoped InnerProductSpace
open FastCLO.ETO

lemma FET_span_top {d : ℕ} (P : Polytope d) (z : FastCLO.ERM.Vec d) (hz : z ∈ P.ext) :
    Submodule.span ℝ (P.A '' {i | ⟪P.A i, z⟫_ℝ = P.b i}) = ⊤ := by
  by_contra hne
  set K := Submodule.span ℝ (P.A '' {i | ⟪P.A i, z⟫_ℝ = P.b i}) with hK
  have hKo : Kᗮ ≠ ⊥ := by
    intro h; apply hne; rwa [Submodule.orthogonal_eq_bot_iff] at h
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKo
  have hvA : ∀ i, ⟪P.A i, z⟫_ℝ = P.b i → ⟪P.A i, v⟫_ℝ = 0 := by
    intro i hi
    have := (Submodule.mem_orthogonal K v).1 hv (P.A i) (Submodule.subset_span ⟨i, hi, rfl⟩)
    exact this
  have hzZ : z ∈ P.Z := hz.1
  have hzi : ∀ i, ⟪P.A i, z⟫_ℝ ≤ P.b i := hzZ
  set S := Finset.univ.filter (fun i => ¬ ⟪P.A i, z⟫_ℝ = P.b i) with hS
  have hslack : ∀ i ∈ S, 0 < P.b i - ⟪P.A i, z⟫_ℝ := by
    intro i hi
    have h1 := hzi i
    have h2 : ¬ ⟪P.A i, z⟫_ℝ = P.b i := (Finset.mem_filter.1 hi).2
    have : ⟪P.A i, z⟫_ℝ < P.b i := lt_of_le_of_ne h1 h2
    linarith
  set K' : ℝ := 1 + ∑ i ∈ S, (|⟪P.A i, v⟫_ℝ| + 1) / (P.b i - ⟪P.A i, z⟫_ℝ) with hK'
  have hK'0 : 0 < K' := by
    have : 0 ≤ ∑ i ∈ S, (|⟪P.A i, v⟫_ℝ| + 1) / (P.b i - ⟪P.A i, z⟫_ℝ) :=
      Finset.sum_nonneg (fun i hi => div_nonneg (by positivity) (hslack i hi).le)
    linarith
  set t : ℝ := 1 / K' with ht
  have ht0 : 0 < t := by positivity
  have hbound : ∀ i ∈ S, t * |⟪P.A i, v⟫_ℝ| ≤ P.b i - ⟪P.A i, z⟫_ℝ := by
    intro i hi
    have h1 : (|⟪P.A i, v⟫_ℝ| + 1) / (P.b i - ⟪P.A i, z⟫_ℝ) ≤ K' := by
      have := Finset.single_le_sum (f := fun i => (|⟪P.A i, v⟫_ℝ| + 1) / (P.b i - ⟪P.A i, z⟫_ℝ))
        (fun i hi => div_nonneg (by positivity) (hslack i hi).le) hi
      linarith
    rw [div_le_iff₀ (hslack i hi)] at h1
    rw [ht, one_div, inv_mul_eq_div, div_le_iff₀ hK'0]
    nlinarith [abs_nonneg ⟪P.A i, v⟫_ℝ]
  have hfeas : ∀ σ : ℝ, |σ| = 1 → z + (σ * t) • v ∈ P.Z := by
    intro σ hσ i
    rw [inner_add_right, inner_smul_right]
    by_cases hi : ⟪P.A i, z⟫_ℝ = P.b i
    · rw [hvA i hi, mul_zero, add_zero]; exact hi.le
    · have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
      have h1 := hbound i hiS
      have h2 : (σ * t) * ⟪P.A i, v⟫_ℝ ≤ t * |⟪P.A i, v⟫_ℝ| := by
        calc (σ * t) * ⟪P.A i, v⟫_ℝ = t * (σ * ⟪P.A i, v⟫_ℝ) := by ring
          _ ≤ t * |σ * ⟪P.A i, v⟫_ℝ| := mul_le_mul_of_nonneg_left (le_abs_self _) ht0.le
          _ = t * |⟪P.A i, v⟫_ℝ| := by rw [abs_mul, hσ, one_mul]
      linarith
  have h1 := hfeas 1 (by simp)
  have h2 := hfeas (-1) (by simp)
  have hseg : z ∈ openSegment ℝ (z + ((1:ℝ) * t) • v) (z + ((-1:ℝ) * t) • v) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    simp only [smul_add, one_mul, neg_mul, neg_smul]
    module
  have := hz.2 h1 h2 hseg
  have h3 : ((1:ℝ) * t) • v = 0 := by
    simpa using this
  rw [one_mul, smul_eq_zero] at h3
  rcases h3 with h | h
  · exact ht0.ne' h
  · exact hv0 h

lemma FET_ext_finite {d : ℕ} (P : Polytope d) : P.ext.Finite := by
  classical
  let act : FastCLO.ERM.Vec d → Finset (Fin P.m) :=
    fun z => Finset.univ.filter (fun i => ⟪P.A i, z⟫_ℝ = P.b i)
  apply Set.Finite.of_injOn (f := act) (t := Set.univ) (fun _ _ => Set.mem_univ _) _ Set.finite_univ
  intro z hz z' hz' h
  have hspan := FET_span_top P z hz
  have hact : ∀ i, ⟪P.A i, z⟫_ℝ = P.b i → ⟪P.A i, z'⟫_ℝ = P.b i := by
    intro i hi
    have : i ∈ act z := by simp [act, hi]
    rw [h] at this
    simpa [act] using this
  let φ : FastCLO.ERM.Vec d →ₗ[ℝ] ℝ := innerₛₗ ℝ (z - z')
  have hle : Submodule.span ℝ (P.A '' {i | ⟪P.A i, z⟫_ℝ = P.b i}) ≤ LinearMap.ker φ := by
    apply Submodule.span_le.2
    rintro _ ⟨i, hi, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, φ, innerₛₗ_apply_apply]
    rw [real_inner_comm, inner_sub_right, hi, hact i hi]; ring
  rw [hspan] at hle
  have h0 : φ (z - z') = 0 := by
    have : z - z' ∈ LinearMap.ker φ := hle Submodule.mem_top
    exact this
  simp only [φ, innerₛₗ_apply_apply, inner_self_eq_zero] at h0
  exact sub_eq_zero.1 h0

theorem solution {p d : ℕ} (P : Polytope d) (I : Instance p d) (f π : FastCLO.ERM.Vec p → FastCLO.ERM.Vec d)
    (hπ : IsPlugIn P f π) (x : FastCLO.ERM.Vec p) (ε : ℝ)
    (hsub : 0 < ⟪I.fstar x, π x⟫_ℝ - optVal P I x) (herr : ‖I.fstar x - f x‖ ≤ ε) :
    0 < gap P I x ∧ gap P I x ≤ 2 * P.B * ε := by
  set u := I.fstar x with hu
  set S : Set ℝ := (fun z => ⟪u, z⟫_ℝ) '' P.Z with hS
  have hZne : P.Z.Nonempty := P.nonempty
  have hSne : S.Nonempty := hZne.image _
  have hSbdd : BddBelow S := by
    refine ⟨-(‖u‖ * P.B), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have h1 : |⟪u, z⟫_ℝ| ≤ ‖u‖ * ‖z‖ := abs_real_inner_le_norm _ _
    have h2 : ‖z‖ ≤ P.B := P.bounded z hz
    have h3 : ‖u‖ * ‖z‖ ≤ ‖u‖ * P.B := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    have := neg_abs_le ⟪u, z⟫_ℝ
    linarith
  have hopt : optVal P I x = sInf S := rfl
  have hπext : π x ∈ P.ext := hπ.1 x
  have hπZ : π x ∈ P.Z := hπext.1
  have hoptle : ∀ z ∈ P.Z, optVal P I x ≤ ⟪u, z⟫_ℝ := by
    intro z hz
    rw [hopt]; exact csInf_le hSbdd ⟨z, hz, rfl⟩
  -- the plug-in decision is not optimal
  have hnot : π x ∉ Zstar P I x := by
    intro h
    have : ⟪u, π x⟫_ℝ ≤ optVal P I x := by
      rw [hopt]
      apply le_csInf hSne
      rintro _ ⟨z, hz, rfl⟩
      exact h.2 z hz
    linarith
  have hne : Zstar P I x ≠ P.Z := fun h => hnot (h ▸ hπZ)
  have hgap : gap P I x = sInf ((fun z => ⟪u, z⟫_ℝ) '' (P.ext \ Zstar P I x)) - optVal P I x := by
    unfold gap; rw [if_neg hne]
  set T : Set ℝ := (fun z => ⟪u, z⟫_ℝ) '' (P.ext \ Zstar P I x) with hT
  have hTfin : T.Finite := ((FET_ext_finite P).subset Set.diff_subset).image _
  have hTne : T.Nonempty := ⟨_, π x, ⟨hπext, hnot⟩, rfl⟩
  constructor
  · rw [hgap]
    obtain ⟨z, ⟨hzext, hznot⟩, hzeq⟩ := hTne.csInf_mem hTfin
    have hzZ : z ∈ P.Z := hzext.1
    have : ∃ z' ∈ P.Z, ⟪u, z'⟫_ℝ < ⟪u, z⟫_ℝ := by
      by_contra hcon
      push Not at hcon
      exact hznot ⟨hzZ, fun z' hz' => hcon z' hz'⟩
    obtain ⟨z', hz', hlt⟩ := this
    have := hoptle z' hz'
    have : optVal P I x < sInf T := by rw [← hzeq]; linarith
    linarith
  · rw [hgap]
    have h1 : sInf T ≤ ⟪u, π x⟫_ℝ := csInf_le hTfin.bddBelow ⟨π x, ⟨hπext, hnot⟩, rfl⟩
    have h2 : ⟪u, π x⟫_ℝ - 2 * P.B * ε ≤ optVal P I x := by
      rw [hopt]
      apply le_csInf hSne
      rintro _ ⟨z₂, hz₂, rfl⟩
      have hb1 : ‖π x‖ ≤ P.B := P.bounded _ hπZ
      have hb2 : ‖z₂‖ ≤ P.B := P.bounded _ hz₂
      have hnorm : ‖π x - z₂‖ ≤ 2 * P.B := by
        calc ‖π x - z₂‖ ≤ ‖π x‖ + ‖z₂‖ := norm_sub_le _ _
          _ ≤ 2 * P.B := by linarith
      have hd : ⟪f x, π x - z₂⟫_ℝ ≤ 0 := by
        rw [inner_sub_right]; linarith [hπ.2 x z₂ hz₂]
      have hd2 : ⟪u - f x, π x - z₂⟫_ℝ ≤ ‖u - f x‖ * ‖π x - z₂‖ := real_inner_le_norm _ _
      have hsplit : ⟪u, π x - z₂⟫_ℝ = ⟪u - f x, π x - z₂⟫_ℝ + ⟪f x, π x - z₂⟫_ℝ := by
        rw [← inner_add_left]; congr 1; abel
      have h3 : ⟪u, π x - z₂⟫_ℝ ≤ 2 * P.B * ε := by
        calc ⟪u, π x - z₂⟫_ℝ ≤ ‖u - f x‖ * ‖π x - z₂‖ := by rw [hsplit]; linarith
          _ ≤ ε * (2 * P.B) := mul_le_mul herr hnorm (norm_nonneg _) (le_trans (norm_nonneg _) herr)
          _ = 2 * P.B * ε := by ring
      rw [inner_sub_right] at h3
      linarith
    linarith
