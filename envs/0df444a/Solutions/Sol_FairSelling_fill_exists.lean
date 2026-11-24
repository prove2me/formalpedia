-- Prove2me | solution 1 for FairSelling.fill_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:12:43.787405+00:00
-- url     : https://prove2.me/submissions/5a36c587-f53b-4a91-bf55-54256627df37

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsBagFilling
import Definitions.Def_RequestProject_TwoThirdsProp6
import Theorems.Thm_FairSelling_fillout_snoc
import Theorems.Thm_FairSelling_fill_one
import Theorems.Thm_FairSelling_exists_minimal_subset_sum
import Theorems.Thm_FairSelling_minimal_bag_le

section
open scoped BigOperators
namespace FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G] [DecidableEq G] in
private lemma vbar_nonneg' {w p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (g : G) : 0 ≤ vbar w p g :=
  le_trans (hp g) (le_max_left _ _)
end FairSelling
end

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ (m : ℕ) (A C S : Finset G) (d r : ℝ) (f₀ : Option G),
      (∀ g ∈ A, ε ≤ vbar w p g) → (∀ g ∈ A, vbar w p g ≤ 2 * ε) →
      (∀ g ∈ C, vbar w p g ≤ ε) →
      (∀ g ∈ S, ε ≤ p g) → (∀ g ∈ S, vbar w p g = p g) →
      Disjoint A C → Disjoint A S → Disjoint C S →
      0 ≤ d → (r = 0 ∨ ε ≤ r) →
      (∀ f, f₀ = some f → f ∉ A ∧ f ∉ C ∧ f ∉ S ∧ r ≤ p f ∧ ε ≤ p f) →
      (f₀ = none → r = 0) →
      A.card ≤ m + 1 → (A.card = m + 1 ∨ (S = ∅ ∧ r = 0)) →
      (m : ℝ) * (3 * ε) + 2 * ε
        ≤ (∑ g ∈ A, vbar w p g) + (∑ g ∈ C, vbar w p g) + d + (∑ g ∈ S, p g) + r →
      Nonempty (FillOut w p ε (m + 1) (A ∪ C ∪ S) d r f₀) := by
  classical
  intro m
  induction m with
  | zero =>
    intro A C S d r f₀ _ _ _ _ hS2 hAC hAS hCS hd hr hf₀ hf₀n _ _ hbud
    exact fill_one w p hp hε A C S d r f₀ hS2 hAC hAS hCS hd hr hf₀ hf₀n (by
      simp only [Nat.cast_zero, zero_mul, zero_add] at hbud
      linarith)
  | succ m ih =>
    intro A C S d r f₀ hA1 hA2 hC1 hS1 hS2 hAC hAS hCS hd hr hf₀ hf₀n hcard hseed hbud
    have hvb0 : ∀ g, 0 ≤ vbar w p g := vbar_nonneg' hp
    have hr0 : 0 ≤ r := by rcases hr with h | h <;> linarith
    by_cases hsale : S = ∅ ∧ r = 0
    · -- **The filling case**: nothing left to sell, the new part is pure.
      obtain ⟨hSe, hre⟩ := hsale
      obtain ⟨Aseed, A', hseedsub, hA'def, hσ1, hσ2, hAsplit, hA'card⟩ :
          ∃ (Aseed A' : Finset G), Aseed ⊆ A ∧ A' = A \ Aseed ∧
            (∀ e ∈ Aseed, ε ≤ vbar w p e) ∧ vbarSum w p Aseed ≤ 2 * ε ∧
            (∑ g ∈ A, vbar w p g) = vbarSum w p Aseed + ∑ g ∈ A', vbar w p g ∧
            A'.card ≤ m + 1 := by
        by_cases hAne : A.Nonempty
        · obtain ⟨a, ha⟩ := hAne
          refine ⟨{a}, A \ {a}, by simpa using ha, rfl, by simpa using hA1 a ha, ?_, ?_, ?_⟩
          · simpa [vbarSum] using hA2 a ha
          · rw [← Finset.sum_sdiff (by simpa using ha : ({a} : Finset G) ⊆ A)]
            simp [vbarSum, add_comm]
          · have : (A \ {a}).card = A.card - 1 := by
              rw [Finset.sdiff_singleton_eq_erase]; exact Finset.card_erase_of_mem ha
            have h1 : 1 ≤ A.card := Finset.card_pos.mpr ⟨a, ha⟩
            omega
        · have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAne
          exact ⟨∅, ∅, by simp, by simp [hAe], by simp, by simp [vbarSum]; linarith,
            by simp [hAe, vbarSum], by simp⟩
      set σ : ℝ := vbarSum w p Aseed with hσdef
      have hσ0 : 0 ≤ σ := Finset.sum_nonneg (fun g _ => hvb0 g)
      set need : ℝ := 2 * ε - σ with hneeddef
      have hneed0 : 0 ≤ need := by simp only [hneeddef]; linarith
      set dnew : ℝ := min d need with hdnewdef
      have hdnew0 : 0 ≤ dnew := le_min hd hneed0
      set rest : ℝ := need - dnew with hrestdef
      have hrest0 : 0 ≤ rest := by
        simp only [hrestdef, hdnewdef, sub_nonneg]; exact min_le_right _ _
      -- the cheap goods suffice to cover what the bank could not
      have hrestC : rest ≤ ∑ g ∈ C, vbar w p g := by
        rcases le_total need d with hle | hlt
        · have : dnew = need := min_eq_right hle
          simp only [hrestdef, this, sub_self]
          exact Finset.sum_nonneg (fun g _ => hvb0 g)
        · have hdn : dnew = d := min_eq_left hlt
          have hA'sum : (∑ g ∈ A', vbar w p g) ≤ ((m : ℝ) + 1) * (2 * ε) := by
            calc (∑ g ∈ A', vbar w p g) ≤ ∑ _g ∈ A', 2 * ε :=
                  Finset.sum_le_sum (fun g hg => hA2 g (by
                    rw [hA'def] at hg; exact (Finset.mem_sdiff.mp hg).1))
              _ = (A'.card : ℝ) * (2 * ε) := by simp [mul_comm]
              _ ≤ ((m : ℝ) + 1) * (2 * ε) := by
                  have : (A'.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hA'card
                  nlinarith
          have hb : ((m : ℝ) + 1) * (3 * ε) + 2 * ε
              ≤ σ + (∑ g ∈ A', vbar w p g) + (∑ g ∈ C, vbar w p g) + d := by
            have := hbud
            rw [hAsplit, hSe, hre] at this
            push_cast at this ⊢
            simp only [Finset.sum_empty] at this
            linarith
          have hm0 : (0 : ℝ) ≤ ((m : ℝ) + 1) * ε := by positivity
          simp only [hrestdef, hdn, hneeddef]
          nlinarith
      obtain ⟨B, hBsub, hBge, hBmin⟩ :=
        exists_minimal_subset_sum (fun g => vbar w p g) rest C hrestC
      have hBle : (∑ g ∈ B, vbar w p g) ≤ rest + ε :=
        minimal_bag_le hrest0 hε (fun g hg => hC1 g (hBsub hg)) hBge hBmin
      have hB0 : 0 ≤ ∑ g ∈ B, vbar w p g := Finset.sum_nonneg (fun g _ => hvb0 g)
      -- the new part
      set Enew : Finset G := Aseed ∪ B with hEnewdef
      have hAseedB : Disjoint Aseed B :=
        Finset.disjoint_of_subset_left hseedsub (Finset.disjoint_of_subset_right hBsub hAC)
      have hEval : vbarSum w p Enew = σ + ∑ g ∈ B, vbar w p g := by
        simp only [hEnewdef, vbarSum, hσdef]
        exact Finset.sum_union hAseedB
      -- the recursive call
      have hC'sum : (∑ g ∈ C \ B, vbar w p g) = (∑ g ∈ C, vbar w p g) - ∑ g ∈ B, vbar w p g :=
        Finset.sum_sdiff_eq_sub hBsub
      have hf₀'rec : ∀ f, f₀ = some f →
          f ∉ A' ∧ f ∉ C \ B ∧ f ∉ S ∧ r ≤ p f ∧ ε ≤ p f := by
        intro f hf
        refine ⟨fun hc => (hf₀ f hf).1 ?_, fun hc => (hf₀ f hf).2.1 (Finset.mem_sdiff.mp hc).1,
          (hf₀ f hf).2.2.1, (hf₀ f hf).2.2.2.1, (hf₀ f hf).2.2.2.2⟩
        rw [hA'def] at hc
        exact (Finset.mem_sdiff.mp hc).1
      have hrec := ih A' (C \ B) S (d - dnew) r f₀
        (fun g hg => hA1 g (by rw [hA'def] at hg; exact (Finset.mem_sdiff.mp hg).1))
        (fun g hg => hA2 g (by rw [hA'def] at hg; exact (Finset.mem_sdiff.mp hg).1))
        (fun g hg => hC1 g (Finset.mem_sdiff.mp hg).1)
        hS1 hS2
        (Finset.disjoint_of_subset_left (by rw [hA'def]; exact Finset.sdiff_subset)
          (Finset.disjoint_of_subset_right Finset.sdiff_subset hAC))
        (Finset.disjoint_of_subset_left (by rw [hA'def]; exact Finset.sdiff_subset) hAS)
        (Finset.disjoint_of_subset_left Finset.sdiff_subset hCS)
        (by simp only [hdnewdef]; rcases le_total d need with h | h
            · simp [min_eq_left h]
            · simp [min_eq_right h]; linarith)
        hr
        hf₀'rec
        hf₀n hA'card (Or.inr ⟨hSe, hre⟩) (by
          rw [hC'sum]
          have := hbud
          rw [hAsplit] at this
          push_cast at this ⊢
          have hcost : σ + (∑ g ∈ B, vbar w p g) + dnew ≤ 3 * ε := by
            simp only [hrestdef] at hBle; simp only [hneeddef] at hBle ⊢; linarith
          linarith)
      obtain ⟨F⟩ := hrec
      refine fillout_snoc w p ε F ?_ ?_ Enew none dnew 0 ?_ ?_ hdnew0 le_rfl (by linarith) ?_
        (Or.inl rfl) (fun h => absurd rfl h) (fun h => absurd rfl h) (fun _ => rfl)
        (fun f hf => absurd hf (by simp)) ?_
      · intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · rcases Finset.mem_union.mp hx with hx | hx
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (by rw [hA'def] at hx; exact (Finset.mem_sdiff.mp hx).1))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_sdiff.mp hx).1)
        · exact Finset.mem_union_right _ hx
      · intro f hf
        exact Finset.mem_union_right _ (by simp [hf])
      · intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hseedsub hx))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hBsub hx))
      · refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
        have hxAC : x ∈ Aseed ∨ x ∈ B := Finset.mem_union.mp hx
        simp only [Option.toFinset_none, Finset.union_empty] at hx'
        rcases Finset.mem_union.mp hx' with hx' | hx'
        · rcases Finset.mem_union.mp hx' with hx' | hx'
          · rcases Finset.mem_union.mp hx' with hx' | hx'
            · rw [hA'def] at hx'
              rcases hxAC with h | h
              · exact (Finset.mem_sdiff.mp hx').2 h
              · exact Finset.disjoint_left.mp hAC (Finset.mem_sdiff.mp hx').1 (hBsub h)
            · rcases hxAC with h | h
              · exact Finset.disjoint_left.mp hAC (hseedsub h) (Finset.mem_sdiff.mp hx').1
              · exact (Finset.mem_sdiff.mp hx').2 h
          · rcases hxAC with h | h
            · exact Finset.disjoint_left.mp hAS (hseedsub h) hx'
            · exact Finset.disjoint_left.mp hCS (hBsub h) hx'
        · obtain ⟨hxA, hxC, -⟩ := hf₀ x (Option.mem_toFinset.mp hx')
          rcases hxAC with h | h
          · exact hxA (hseedsub h)
          · exact hxC (hBsub h)
      · rw [hEval]
        simp only [hrestdef, hneeddef] at hBge
        simp only [hneeddef, hdnewdef] at *
        linarith
      · intro f
        simp only [reduceCtorEq, if_false, zero_add]
        by_cases hmem : f ∈ F.sell
        · rw [if_pos hmem]
        · rw [if_neg hmem]
          split
          · exact hr0
          · exact hp f
    · -- **The cascade case**: the new part is a singleton funded by the sale of one good.
      have hAcard : A.card = m + 1 + 1 := by
        rcases hseed with h | h
        · exact h
        · exact absurd h hsale
      obtain ⟨a, ha⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
      -- the good that is being sold, and the proceeds available from it
      obtain ⟨f, r₁, S', hfA, hfC, hfS', hr₁ε, hr₁p, hpf, hS'sub, hbudeq, hr₁le, hfmem⟩ :
          ∃ (f : G) (r₁ : ℝ) (S' : Finset G),
            f ∉ A ∧ f ∉ C ∧ f ∉ S' ∧ ε ≤ r₁ ∧ r₁ ≤ p f ∧ ε ≤ p f ∧ S' ⊆ S ∧
            (∑ g ∈ S', p g) + r₁ = (∑ g ∈ S, p g) + r ∧
            r₁ ≤ (if f₀ = some f then r else p f) ∧ f ∈ (A ∪ C ∪ S) ∪ f₀.toFinset := by
        by_cases hr' : r = 0
        · have hSne : S.Nonempty := by
            rcases Finset.eq_empty_or_nonempty S with h | h
            · exact absurd ⟨h, hr'⟩ hsale
            · exact h
          obtain ⟨f, hf⟩ := hSne
          refine ⟨f, p f, S.erase f, fun hc => Finset.disjoint_left.mp hAS hc hf,
            fun hc => Finset.disjoint_left.mp hCS hc hf, Finset.notMem_erase _ _,
            hS1 f hf, le_rfl, hS1 f hf, Finset.erase_subset _ _, ?_, ?_, ?_⟩
          · rw [Finset.sum_erase_add _ _ hf, hr', add_zero]
          · rcases Option.eq_none_or_eq_some f₀ with h' | ⟨f', h'⟩
            · simp [h']
            · have : f' ≠ f := fun hc => (hf₀ f' h').2.2.1 (hc ▸ hf)
              rw [if_neg (by rw [h']; simpa using this)]
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ hf)
        · obtain ⟨f, hf⟩ : ∃ f, f₀ = some f := by
            rcases Option.eq_none_or_eq_some f₀ with h' | h'
            · exact absurd (hf₀n h') hr'
            · exact h'
          obtain ⟨hfA, hfC, hfS, hrp, hpf⟩ := hf₀ f hf
          refine ⟨f, r, S, hfA, hfC, hfS, ?_, hrp, hpf, Finset.Subset.refl _, rfl, ?_, ?_⟩
          · rcases hr with h | h
            · exact absurd h hr'
            · exact h
          · rw [if_pos hf]
          · exact Finset.mem_union_right _ (by simp [hf])
      set σ : ℝ := vbar w p a with hσdef
      have hσ1 : ε ≤ σ := hA1 a ha
      have hσ2 : σ ≤ 2 * ε := hA2 a ha
      set snew : ℝ := if r₁ ≤ 3 * ε - σ then r₁ else 2 * ε - σ with hsnewdef
      set r' : ℝ := r₁ - snew with hr'def
      have hsnew0 : 0 ≤ snew := by
        simp only [hsnewdef]; split
        · linarith
        · linarith
      have hr'0 : 0 ≤ r' := by
        simp only [hr'def, hsnewdef]; split
        · simp
        · rename_i hc; push_neg at hc; linarith
      have hr'cases : r' = 0 ∨ ε ≤ r' := by
        simp only [hr'def, hsnewdef]; split
        · left; ring
        · rename_i hc; push_neg at hc; right; linarith
      have hacc : 2 * ε ≤ σ + snew := by
        simp only [hsnewdef]; split
        · linarith
        · linarith
      have hcost : σ + snew ≤ 3 * ε := by
        simp only [hsnewdef]; split
        · rename_i hc; linarith
        · linarith
      -- the recursive call
      have hA'card : (A.erase a).card = m + 1 := by
        rw [Finset.card_erase_of_mem ha, hAcard]
        omega
      have hrec := ih (A.erase a) C S' (d) r' (some f)
        (fun g hg => hA1 g (Finset.mem_of_mem_erase hg))
        (fun g hg => hA2 g (Finset.mem_of_mem_erase hg))
        hC1 (fun g hg => hS1 g (hS'sub hg)) (fun g hg => hS2 g (hS'sub hg))
        (Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hAC)
        (Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
          (Finset.disjoint_of_subset_right hS'sub hAS))
        (Finset.disjoint_of_subset_right hS'sub hCS)
        hd hr'cases
        (fun f' hf' => by
          have : f' = f := by simpa using hf'.symm
          subst this
          exact ⟨fun hc => hfA (Finset.mem_of_mem_erase hc), hfC, hfS',
            le_trans (by simp only [hr'def]; linarith) hr₁p, hpf⟩)
        (by simp) (by omega) (Or.inl hA'card)
        (by
          have hAsum : (∑ g ∈ A, vbar w p g) = σ + ∑ g ∈ A.erase a, vbar w p g := by
            rw [hσdef, Finset.add_sum_erase _ _ ha]
          have := hbud
          rw [hAsum] at this
          push_cast at this ⊢
          simp only [hr'def]
          linarith [hbudeq]
          )
      obtain ⟨F⟩ := hrec
      refine fillout_snoc w p ε F ?_ ?_ {a} (some f) 0 snew ?_ ?_ le_rfl hsnew0 (by linarith)
        ?_ (Or.inr ⟨a, rfl⟩) (fun _ => rfl) ?_ (fun h => absurd h (by simp)) ?_ ?_
      · intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · rcases Finset.mem_union.mp hx with hx | hx
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_of_mem_erase hx))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
        · exact Finset.mem_union_right _ (hS'sub hx)
      · intro f' hf'
        have : f' = f := by simpa using hf'.symm
        subst this; exact hfmem
      · simp only [Finset.singleton_subset_iff]
        exact Finset.mem_union_left _ (Finset.mem_union_left _ ha)
      · refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
        have hxa : x = a := by simpa using hx
        subst hxa
        rcases Finset.mem_union.mp hx' with hx' | hx'
        · rcases Finset.mem_union.mp hx' with hx' | hx'
          · rcases Finset.mem_union.mp hx' with hx' | hx'
            · rcases Finset.mem_union.mp hx' with hx' | hx'
              · exact (Finset.notMem_erase _ _) hx'
              · exact Finset.disjoint_left.mp hAC ha hx'
            · exact Finset.disjoint_left.mp hAS ha (hS'sub hx')
          · have haf : x = f := by simpa using hx'
            exact hfA (haf ▸ ha)
        · have haf : x = f := by simpa using hx'
          exact hfA (haf ▸ ha)
      · simp only [vbarSum, Finset.sum_singleton, ← hσdef]
        linarith
      · intro _ e he
        have : e = a := by simpa using he
        subst this; exact hσ1
      · intro f' hf'
        have : f' = f := by simpa using hf'.symm
        subst this
        refine ⟨fun hc => ?_, hpf, hfmem⟩
        rcases Finset.mem_union.mp hc with hc | hc
        · rcases Finset.mem_union.mp hc with hc | hc
          · exact hfA (Finset.mem_of_mem_erase hc)
          · exact hfC hc
        · exact hfS' hc
      · intro f'
        by_cases hff : f' = f
        · subst hff
          rw [if_pos rfl]
          have h1 : (if f' ∈ F.sell then (if some f' = some f' then r' else p f') else 0) ≤ r' := by
            split
            · rw [if_pos rfl]
            · exact hr'0
          have : snew + r' = r₁ := by simp only [hr'def]; ring
          linarith [hr₁le]
        · rw [if_neg (by simpa using fun hc => hff hc.symm)]
          rw [zero_add]
          by_cases hmem : f' ∈ F.sell
          · rw [if_pos hmem, if_neg (by simpa using fun hc => hff hc.symm)]
            have hnot : f₀ ≠ some f' := by
              intro hc
              obtain ⟨hA', hC', hS'', -⟩ := hf₀ f' hc
              rcases Finset.mem_union.mp (F.sell_subset hmem) with hx | hx
              · rcases Finset.mem_union.mp hx with hx | hx
                · rcases Finset.mem_union.mp hx with hx | hx
                  · exact hA' (Finset.mem_of_mem_erase hx)
                  · exact hC' hx
                · exact hS'' (hS'sub hx)
              · exact hff (by simpa using hx)
            rw [if_neg hnot]
          · rw [if_neg hmem]
            split
            · exact hr0
            · exact hp f'
end FairSelling
