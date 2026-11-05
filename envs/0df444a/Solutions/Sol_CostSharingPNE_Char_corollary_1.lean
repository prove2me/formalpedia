-- Prove2me | solution 1 for CostSharingPNE.Char.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:46:14.940572+00:00
-- url     : https://prove2.me/submissions/2abf75c6-6b8d-4ca3-a9fe-3ac565ac5d7b

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Definitions.Def_CostSharingPNE_Char_Basis
import Theorems.Thm_CostSharingPNE_Char_lemma_7

open CostSharingPNE.Char

namespace CSPCor1Aux

variable {n : ℕ}

lemma coalitionsIn_sub (W : Welfare n) {S X : Finset (Fin n)} (hX : X ⊆ S) :
    coalitionsIn W X = (coalitionsIn W S).filter (fun T => T ⊆ X) := by
  ext T
  unfold coalitionsIn
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hX⟩, h2⟩
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩

/-! ### Möbius coefficients of the poset `(𝒞, ⊆)` below a top element -/

/-- `m(T) = [T = top] - ∑_{T' ∈ 𝒞, T ⊊ T'} m(T')`, so that
`∑_{T ∈ 𝒞, T'' ⊆ T} m(T) = [T'' = top]` for `T'' ∈ 𝒞`. -/
def mcoef (𝒞 : Finset (Finset (Fin n))) (top T : Finset (Fin n)) : ℤ :=
  (if T = top then 1 else 0) - ∑ T' ∈ (𝒞.filter (fun T' => T ⊂ T')).attach, mcoef 𝒞 top T'.1
termination_by n + 1 - T.card
decreasing_by
  have h := T'.2
  rw [Finset.mem_filter] at h
  have h1 := Finset.card_lt_card h.2
  have h2 : T'.1.card ≤ n := by
    have := Finset.card_le_univ T'.1
    simpa using this
  omega

lemma mcoef_sum (𝒞 : Finset (Finset (Fin n))) (top T'' : Finset (Fin n)) (h : T'' ∈ 𝒞) :
    ∑ T ∈ 𝒞.filter (fun T => T'' ⊆ T), mcoef 𝒞 top T = if T'' = top then 1 else 0 := by
  have hsplit : 𝒞.filter (fun T => T'' ⊆ T) = insert T'' (𝒞.filter (fun T => T'' ⊂ T)) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hT, hs⟩
      by_cases he : T = T''
      · left; exact he
      · right; exact ⟨hT, Finset.ssubset_iff_subset_ne.mpr ⟨hs, Ne.symm he⟩⟩
    · rintro (rfl | ⟨hT, hs⟩)
      · exact ⟨h, Finset.Subset.refl _⟩
      · exact ⟨hT, hs.subset⟩
  rw [hsplit, Finset.sum_insert (by simp)]
  rw [mcoef]
  rw [Finset.sum_attach (𝒞.filter (fun T' => T'' ⊂ T')) (fun T' => mcoef 𝒞 top T')]
  ring

lemma swap_sum_m (𝒞 : Finset (Finset (Fin n))) (top : Finset (Fin n))
    (h : Finset (Fin n) → ℝ) (P : Finset (Fin n) → Prop) [DecidablePred P] :
    ∑ T ∈ 𝒞, (mcoef 𝒞 top T : ℝ) * ∑ T'' ∈ 𝒞.filter (fun T'' => T'' ⊆ T ∧ P T''), h T'' =
      ∑ T'' ∈ 𝒞.filter P, (if T'' = top then h T'' else 0) := by
  simp_rw [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T'' hT''
  by_cases hP : P T''
  · rw [if_pos hP]
    have : ∀ T ∈ 𝒞, (mcoef 𝒞 top T : ℝ) * (if T'' ⊆ T ∧ P T'' then h T'' else 0) =
        (if T'' ⊆ T then (mcoef 𝒞 top T : ℝ) else 0) * h T'' := by
      intro T _
      by_cases hs : T'' ⊆ T
      · simp [hs, hP]
      · simp [hs]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← Finset.sum_filter]
    rw [← Int.cast_sum, mcoef_sum 𝒞 top T'' hT'']
    split_ifs <;> simp
  · rw [if_neg hP]
    apply Finset.sum_eq_zero
    intro T _
    simp [hP]

/-! ### Lemma 4 for the basis rules -/

lemma basis_unfold (g : Rule n) (W : Welfare n) (T : Finset (Fin n)) (i : Fin n)
    (S : Finset (Fin n)) : basisRule g W T i S = if T ⊆ S then
      (1 / mobius W T) * (g i T - ∑ T' ∈ ((coalitionsIn W T).erase T).attach,
        mobius W T'.1 * basisRule g W T'.1 i S) else 0 := by
  rw [basisRule]

lemma mem_erase_coal {W : Welfare n} {T : Finset (Fin n)} (T' : Finset (Fin n))
    (h : T' ∈ (coalitionsIn W T).erase T) : T' ⊂ T ∧ T' ∈ coalitions W := by
  rw [Finset.mem_erase] at h
  unfold coalitionsIn at h
  rw [Finset.mem_filter] at h
  exact ⟨Finset.ssubset_iff_subset_ne.mpr ⟨h.2.2, h.1⟩, h.2.1⟩

/-- Lemma 4, first part: `f^T(i,S) = f^T(i,T)` whenever `T ⊆ S`. -/
lemma basis_local (g : Rule n) (W : Welfare n) (i : Fin n) :
    ∀ T S : Finset (Fin n), T ⊆ S → basisRule g W T i S = basisRule g W T i T := by
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
    intro S hTS
    rw [basis_unfold g W T i S, basis_unfold g W T i T, if_pos hTS, if_pos (subset_refl T)]
    congr 2
    apply Finset.sum_congr rfl
    intro T' _
    have h := mem_erase_coal T'.1 T'.2
    rw [ih T'.1 h.1 S (h.1.subset.trans hTS), ih T'.1 h.1 T h.1.subset]

/-- Lemma 4, second part: `f^T(i,T) = 0` for `i ∉ T`. -/
lemma basis_out (g : Rule n) (W : Welfare n) (h0 : ∀ i S, i ∉ S → g i S = 0) (i : Fin n) :
    ∀ T : Finset (Fin n), i ∉ T → basisRule g W T i T = 0 := by
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
    intro hi
    rw [basis_unfold g W T i T, if_pos (subset_refl T), h0 i T hi]
    have : ∑ T' ∈ ((coalitionsIn W T).erase T).attach, mobius W T'.1 * basisRule g W T'.1 i T
        = 0 := by
      apply Finset.sum_eq_zero
      intro T' _
      have h := mem_erase_coal T'.1 T'.2
      rw [basis_local g W i T'.1 T h.1.subset, ih T'.1 h.1 (fun hh => hi (h.1.subset hh))]
      ring
    rw [this]; ring

/-- `G(k, X) = ∑_{T ∈ 𝒯(X)} q_T f^T(k, T)`. -/
noncomputable def G (g : Rule n) (W : Welfare n) (k : Fin n) (X : Finset (Fin n)) : ℝ :=
  ∑ T ∈ coalitionsIn W X, mobius W T * basisRule g W T k T

lemma rhs_eq_G (g : Rule n) (W : Welfare n) (k : Fin n) (S : Finset (Fin n)) :
    ∑ T ∈ coalitions W, mobius W T * basisRule g W T k S = G g W k S := by
  unfold G coalitionsIn
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hTS : T ⊆ S
  · rw [if_pos hTS, basis_local g W k T S hTS]
  · rw [if_neg hTS, basis_unfold, if_neg hTS, mul_zero]

end CSPCor1Aux

open CSPCor1Aux in
theorem solution (n : ℕ) (hn : 1 < n) (W : Welfare n) (f : Welfare n → Rule n)
    (hbb : IsBudgetBalanced (f W) W) (hpne : GuaranteesPNE {W} f)
    (h0 : ∀ i S, i ∉ S → f W i S = 0) :
    ∀ T ∈ coalitions W, ∃ c : Finset (Fin n) → ℤ,
      (∀ i ∈ T, mobius W T * basisRule (f W) W T i T =
          ∑ T' ∈ coalitionsIn W T, (c T' : ℝ) * f W i T') ∧
      (∀ i ∈ T, ∀ j ∈ T, j ≠ i →
          0 = mobius W T * basisRule (f W) W T i (T.erase j) ∧
          mobius W T * basisRule (f W) W T i (T.erase j) =
            ∑ T' ∈ coalitionsIn W T, (c T' : ℝ) * f W i (T'.erase j)) := by
  intro T hT
  set 𝒞 := coalitionsIn W T with h𝒞def
  have hT𝒞 : T ∈ 𝒞 := by
    unfold 𝒞 coalitionsIn; exact Finset.mem_filter.mpr ⟨hT, Finset.Subset.refl T⟩
  -- `f = G` everywhere (Lemma 7 together with Lemma 4)
  have hfG : ∀ (x : Fin n) (X : Finset (Fin n)), f W x X =
      ∑ T'' ∈ coalitionsIn W X, mobius W T'' * basisRule (f W) W T'' x T'' := by
    intro x X
    by_cases hx : x ∈ X
    · rw [lemma_7 n hn W f hbb hpne h0 X x hx]
      unfold coalitionsIn
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro T' _
      by_cases hTX : T' ⊆ X
      · rw [if_pos hTX, basis_local (f W) W x T' X hTX]
      · rw [if_neg hTX, basis_unfold, if_neg hTX, mul_zero]
    · rw [h0 x X hx]
      symm
      apply Finset.sum_eq_zero
      intro T' hT'
      have hTX : T' ⊆ X := by unfold coalitionsIn at hT'; exact (Finset.mem_filter.mp hT').2
      rw [basis_out (f W) W h0 x T' (fun h => hx (hTX h)), mul_zero]
  have h𝒞 : ∀ T' ∈ 𝒞, T' ⊆ T := by
    intro T' hT'; unfold 𝒞 coalitionsIn at hT'; exact (Finset.mem_filter.mp hT').2
  refine ⟨mcoef 𝒞 T, ?_, ?_⟩
  · intro i _
    have e1 : ∀ T' ∈ 𝒞, (mcoef 𝒞 T T' : ℝ) * f W i T' = (mcoef 𝒞 T T' : ℝ) *
        ∑ T'' ∈ 𝒞.filter (fun T'' => T'' ⊆ T' ∧ True),
          mobius W T'' * basisRule (f W) W T'' i T'' := by
      intro T' hT'
      rw [hfG i T', coalitionsIn_sub W (h𝒞 T' hT')]
      congr 1
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext; simp [h𝒞def]
    rw [Finset.sum_congr rfl e1, swap_sum_m]
    rw [Finset.filter_true_of_mem (fun _ _ => trivial), Finset.sum_ite_eq' 𝒞 T, if_pos hT𝒞]
  · intro i _ j hj _
    have hz : basisRule (f W) W T i (T.erase j) = 0 := by
      rw [basis_unfold, if_neg]
      intro h
      exact Finset.notMem_erase j T (h hj)
    rw [hz, mul_zero]
    refine ⟨rfl, ?_⟩
    have e1 : ∀ T' ∈ 𝒞, (mcoef 𝒞 T T' : ℝ) * f W i (T'.erase j) = (mcoef 𝒞 T T' : ℝ) *
        ∑ T'' ∈ 𝒞.filter (fun T'' => T'' ⊆ T' ∧ j ∉ T''),
          mobius W T'' * basisRule (f W) W T'' i T'' := by
      intro T' hT'
      rw [hfG i _, coalitionsIn_sub W ((Finset.erase_subset j T').trans (h𝒞 T' hT'))]
      congr 1
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext T''; simp only [Finset.mem_filter, Finset.subset_erase, h𝒞def]
    rw [Finset.sum_congr rfl e1, swap_sum_m]
    symm
    apply Finset.sum_eq_zero
    intro T'' hT''
    rw [Finset.mem_filter] at hT''
    rw [if_neg]
    rintro rfl
    exact hT''.2 hj
