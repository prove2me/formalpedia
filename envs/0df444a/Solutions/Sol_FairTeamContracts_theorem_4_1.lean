-- Prove2me | solution 1 for FairTeamContracts.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-20T02:39:23.322804+00:00
-- url     : https://prove2.me/submissions/40494120-cf01-4c6d-901b-795f6d9ca88a

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_FairTeamContracts_IsSuccessFn
import Definitions.Def_FairTeamContracts_IsAdditive
import Definitions.Def_FairTeamContracts_optFair
import Definitions.Def_FairTeamContracts_optND

namespace FairTeamContracts_Proof

open FairTeamContracts

/-! ### Section 1: The Cubic `ρ³ - ρ² - 2ρ + 1 = 0` on `(0, 1)` -/

section Cubic

private def cubicG (x : ℝ) : ℝ := x ^ 3 - x ^ 2 - 2 * x + 1

private lemma cubicG_sub (x y : ℝ) :
    cubicG x - cubicG y = (x - y) * (x ^ 2 + x * y + y ^ 2 - x - y - 2) := by
  dsimp [cubicG]
  ring

private lemma cubicG_strictAntiOn : StrictAntiOn cubicG (Set.Icc (0 : ℝ) 1) := by
  rintro x ⟨hx0, hx1⟩ y ⟨hy0, hy1⟩ hxy
  have hsq_x : x ^ 2 ≤ x := by nlinarith only [hx0, hx1]
  have hsq_y : y ^ 2 ≤ y := by nlinarith only [hy0, hy1]
  have hxy_le : x * y ≤ 1 := by nlinarith only [hx0, hx1, hy0, hy1]
  have hfac_neg : x ^ 2 + x * y + y ^ 2 - x - y - 2 < 0 := by linarith
  have hdiff_pos : 0 < cubicG x - cubicG y := by
    rw [cubicG_sub]
    nlinarith only [hxy, hfac_neg]
  linarith

private lemma exists_unique_cubic_root :
    ∃! ρ : ℝ, ρ ∈ Set.Ioo (0 : ℝ) 1 ∧ ρ ^ 3 - ρ ^ 2 - 2 * ρ + 1 = 0 := by
  have hcont : Continuous cubicG := by
    unfold cubicG
    continuity
  have hmem : (0 : ℝ) ∈ cubicG '' Set.Icc (0 : ℝ) 1 :=
    intermediate_value_Icc' (by norm_num) hcont.continuousOn
      ⟨by norm_num [cubicG], by norm_num [cubicG]⟩
  rcases hmem with ⟨ρ, ⟨hρ0, hρ1⟩, hρ_eq⟩
  have hρ_ne0 : ρ ≠ 0 := by
    rintro rfl
    norm_num [cubicG] at hρ_eq
  have hρ_ne1 : ρ ≠ 1 := by
    rintro rfl
    norm_num [cubicG] at hρ_eq
  have hρ_ioo : ρ ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hρ0 hρ_ne0.symm, lt_of_le_of_ne hρ1 hρ_ne1⟩
  refine ⟨ρ, ⟨hρ_ioo, hρ_eq⟩, ?_⟩
  rintro y ⟨hy_ioo, hy_eq⟩
  have hy_icc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy_ioo
  have hρ_icc : ρ ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hρ_ioo
  exact cubicG_strictAntiOn.injOn hy_icc hρ_icc (hy_eq.trans hρ_eq.symm)

private lemma cubic_root_props {ρ : ℝ} (hρ_ioo : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (hρ_eq : ρ ^ 3 - ρ ^ 2 - 2 * ρ + 1 = 0) :
    (4 / 9 : ℝ) < ρ ∧ ρ < (1 / 2 : ℝ) ∧
    ρ * (2 - ρ) * (1 + ρ) = 1 ∧ 1 < (17 / 24 : ℝ) * (1 + ρ) := by
  have hρ_icc : ρ ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hρ_ioo
  have hgρ : cubicG ρ = 0 := hρ_eq
  have h49_lt : (4 / 9 : ℝ) < ρ := by
    rcases lt_or_ge (4 / 9 : ℝ) ρ with hlt | hle
    · exact hlt
    · exfalso
      have h49_icc : (4 / 9 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
      have hg49_pos : (0 : ℝ) < cubicG (4 / 9) := by norm_num [cubicG]
      rcases eq_or_lt_of_le hle with rfl | hlt
      · linarith
      · have := cubicG_strictAntiOn hρ_icc h49_icc hlt
        linarith
  have h12_gt : ρ < (1 / 2 : ℝ) := by
    rcases lt_or_ge ρ (1 / 2 : ℝ) with hlt | hge
    · exact hlt
    · exfalso
      have h12_icc : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
      have hg12_neg : cubicG (1 / 2) < 0 := by norm_num [cubicG]
      rcases eq_or_lt_of_le hge with heq | hlt
      · rw [← heq] at hgρ
        linarith
      · have := cubicG_strictAntiOn h12_icc hρ_icc hlt
        linarith
  have hprod : ρ * (2 - ρ) * (1 + ρ) = 1 := by
    have hid : ρ * (2 - ρ) * (1 + ρ) - 1 = -(ρ ^ 3 - ρ ^ 2 - 2 * ρ + 1) := by ring
    linarith
  refine ⟨h49_lt, h12_gt, hprod, by linarith⟩

end Cubic

/-! ### Section 2: Additivity Implies Submodularity & Basic Contract Bounds -/

lemma isSubmodular_of_isAdditive {n : ℕ} {f : Finset (Fin n) → ℝ} (hadd : IsAdditive f) :
    SubsamplingSM.Offline.IsSubmodular f := by
  intro A B e hAB heB
  have heA : e ∉ A := fun heA => heB (hAB heA)
  rw [hadd (insert e B), hadd B, hadd (insert e A), hadd A,
      Finset.sum_insert heB, Finset.sum_insert heA]
  linarith

section BasicBounds

private lemma empty_isNonDiscr {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ) :
    IsNonDiscr f c ∅ (fun _ => 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro i hi <;> simp at hi

private lemma empty_isFair {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ) :
    IsFair f c ∅ (fun _ => 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro i hi <;> simp at hi

private lemma rev_le_one {n : ℕ} {f : Finset (Fin n) → ℝ} (hf : IsSuccessFn f)
    {S : Finset (Fin n)} {α : Fin n → ℝ} (hTC : IsTeamContract S α) :
    rev f S α ≤ 1 := by
  unfold rev
  have hsum_nonneg : 0 ≤ ∑ i ∈ S, α i :=
    Finset.sum_nonneg (fun i hi => (hTC i hi).1)
  have hf_nonneg : 0 ≤ f S := (hf.2.2 S).1
  have hf_le1 : f S ≤ 1 := (hf.2.2 S).2
  nlinarith only [hsum_nonneg, hf_nonneg, hf_le1]

private lemma bddAbove_ndSet {n : ℕ} {f : Finset (Fin n) → ℝ} (hf : IsSuccessFn f)
    (c : Fin n → ℝ) :
    BddAbove {r : ℝ | ∃ (S : Finset (Fin n)) (α : Fin n → ℝ), IsNonDiscr f c S α ∧ rev f S α = r} := by
  refine ⟨1, ?_⟩
  rintro r ⟨S, α, hND, rfl⟩
  exact rev_le_one hf hND.1

private lemma nonempty_ndSet {n : ℕ} {f : Finset (Fin n) → ℝ} (hf : IsSuccessFn f)
    (c : Fin n → ℝ) :
    ({r : ℝ | ∃ (S : Finset (Fin n)) (α : Fin n → ℝ), IsNonDiscr f c S α ∧ rev f S α = r}).Nonempty := by
  refine ⟨0, ∅, fun _ => 0, empty_isNonDiscr f c, ?_⟩
  simp [rev, hf.2.1]

private lemma nonempty_fairSet {n : ℕ} {f : Finset (Fin n) → ℝ} (hf : IsSuccessFn f)
    (c : Fin n → ℝ) :
    ({r : ℝ | ∃ (S : Finset (Fin n)) (α : Fin n → ℝ), IsFair f c S α ∧ rev f S α = r}).Nonempty := by
  refine ⟨0, ∅, fun _ => 0, empty_isFair f c, ?_⟩
  simp [rev, hf.2.1]

private lemma bddAbove_fairSet {n : ℕ} {f : Finset (Fin n) → ℝ} (hf : IsSuccessFn f)
    (c : Fin n → ℝ) :
    BddAbove {r : ℝ | ∃ (S : Finset (Fin n)) (α : Fin n → ℝ), IsFair f c S α ∧ rev f S α = r} := by
  refine ⟨1, ?_⟩
  rintro r ⟨S, α, hF, rfl⟩
  exact rev_le_one hf hF.1

private lemma rev_le_optND {n : ℕ} {f : Finset (Fin n) → ℝ} (hf : IsSuccessFn f)
    {c : Fin n → ℝ} {S : Finset (Fin n)} {α : Fin n → ℝ} (hND : IsNonDiscr f c S α) :
    rev f S α ≤ optND f c :=
  le_csSup (bddAbove_ndSet hf c) ⟨S, α, hND, rfl⟩

private lemma rev_le_optFair {n : ℕ} {f : Finset (Fin n) → ℝ} (hf : IsSuccessFn f)
    {c : Fin n → ℝ} {S : Finset (Fin n)} {α : Fin n → ℝ} (hFair : IsFair f c S α) :
    rev f S α ≤ optFair f c :=
  le_csSup (bddAbove_fairSet hf c) ⟨S, α, hFair, rfl⟩

private lemma optND_nonneg {n : ℕ} {f : Finset (Fin n) → ℝ} (hf : IsSuccessFn f)
    (c : Fin n → ℝ) :
    0 ≤ optND f c := by
  have hrev0 : rev f ∅ (fun _ => 0) = 0 := by simp [rev, hf.2.1]
  rw [← hrev0]
  exact rev_le_optND hf (empty_isNonDiscr f c)

/-- Uniform non-discriminatory contract on `T ⊆ S` with common share `q ≥ max_{k ∈ T} α_k`. -/
private lemma uniform_subset_le_optND {n : ℕ} {f : Finset (Fin n) → ℝ} {c : Fin n → ℝ}
    (hf : IsSuccessFn f) (hsub : SubsamplingSM.Offline.IsSubmodular f)
    {S : Finset (Fin n)} {α : Fin n → ℝ} (hFeas : IsFeasible f c S α)
    {T : Finset (Fin n)} (hTS : T ⊆ S) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hqT : ∀ k ∈ T, α k ≤ q) :
    (1 - (T.card : ℝ) * q) * f T ≤ optND f c := by
  have hND : IsNonDiscr f c T (fun _ => q) := by
    refine ⟨fun _ _ => ⟨hq0, hq1⟩, ?_, fun _ _ _ _ => rfl⟩
    intro k hkT
    have hkS : k ∈ S := hTS hkT
    have hsub_erase : T.erase k ⊆ S.erase k := Finset.erase_subset_erase k hTS
    have hk_not : k ∉ S.erase k := by simp
    have hsm := hsub (T.erase k) (S.erase k) k hsub_erase hk_not
    rw [Finset.insert_erase hkS, Finset.insert_erase hkT] at hsm
    have hmarg_nonneg : 0 ≤ f S - f (S.erase k) := by
      have := hf.1 (S.erase k) S (Finset.erase_subset k S)
      linarith
    have hfk := hFeas k hkS
    have hαq := hqT k hkT
    nlinarith only [hsm, hmarg_nonneg, hfk, hαq, hq0]
  have hrev : rev f T (fun _ => q) = (1 - (T.card : ℝ) * q) * f T := by
    simp [rev]
  rw [← hrev]
  exact rev_le_optND hf hND

/-- Division-free fairness swap inequality (Proposition 2.5 + Lemma 3.3 + Lemma 3.4 only-if). -/
private lemma fair_swap_ineq {n : ℕ} {f : Finset (Fin n) → ℝ} {c : Fin n → ℝ}
    (hf : IsSuccessFn f) (hsub : SubsamplingSM.Offline.IsSubmodular f)
    {S : Finset (Fin n)} {α : Fin n → ℝ} (hFair : IsFair f c S α)
    (hfS : 0 < f S) {i j : Fin n} (hi : i ∈ S) (hj : j ∈ S) :
    α j * f (S.erase j) ≤ α i * f S := by
  rcases hFair with ⟨hTC, hFeas, hSwap⟩
  rcases lt_or_ge (α i) (α j) with hlt | hge
  · have hij : i ≠ j := fun h => by subst h; linarith
    obtain ⟨E, ⟨hES, _, hPNE_out⟩, hUi, _⟩ := hSwap i hi j hj
    have hsubE : S.erase j ⊆ E := by
      intro k hk
      rcases Finset.mem_erase.mp hk with ⟨hk_ne_j, hkS⟩
      by_contra hkE
      let α' : Fin n → ℝ := α ∘ Equiv.swap i j
      have hα_le : α k ≤ α' k := by
        dsimp [α']
        by_cases hki : k = i
        · subst hki
          rw [Equiv.swap_apply_left]
          exact le_of_lt hlt
        · rw [Equiv.swap_apply_of_ne_of_ne hki hk_ne_j]
      have hE_erase : E ⊆ S.erase k := by
        intro x hx
        exact Finset.mem_erase.mpr ⟨by rintro rfl; exact hkE hx, hES hx⟩
      have hk_not : k ∉ S.erase k := by simp
      have hsm := hsub E (S.erase k) k hE_erase hk_not
      rw [Finset.insert_erase hkS] at hsm
      have hmarg_nonneg : 0 ≤ f S - f (S.erase k) := by
        have := hf.1 (S.erase k) S (Finset.erase_subset k S)
        linarith
      have hfk := hFeas k hkS
      have hout := hPNE_out k (Finset.mem_sdiff.mpr ⟨hkS, hkE⟩)
      change α' k * f (insert k E) - c k < α' k * f E at hout
      have hα0 : 0 ≤ α k := (hTC k hkS).1
      nlinarith only [hsm, hmarg_nonneg, hfk, hout, hα_le, hα0]
    have hjE : j ∉ E := by
      intro hjE
      have hSE : S ⊆ E := by
        rw [← Finset.insert_erase hj]
        exact Finset.insert_subset_iff.mpr ⟨hjE, hsubE⟩
      have hES_eq : E = S := Finset.Subset.antisymm hES hSE
      rw [hES_eq, if_pos hi] at hUi
      nlinarith only [hlt, hfS, hUi]
    have hE_eq : E = S.erase j :=
      Finset.Subset.antisymm
        (fun x hx => Finset.mem_erase.mpr ⟨by rintro rfl; exact hjE hx, hES hx⟩)
        hsubE
    have hiE : i ∈ E := by
      rw [hE_eq]
      exact Finset.mem_erase.mpr ⟨hij, hi⟩
    rw [if_pos hiE, hE_eq] at hUi
    linarith
  · have hαj0 : 0 ≤ α j := (hTC j hj).1
    have hf_erase0 : 0 ≤ f (S.erase j) := (hf.2.2 (S.erase j)).1
    have hf_mono : f (S.erase j) ≤ f S := hf.1 (S.erase j) S (Finset.erase_subset j S)
    exact mul_le_mul hge hf_mono hf_erase0 (le_trans hαj0 hge)

end BasicBounds

/-! ### Section 3: Submodular XOS Weights & Subset Averaging -/

section Combinatorics

/-- Every monotone normalized submodular function admits nonnegative additive weights on `S`
summing to `f S` and minorizing `f` on all subsets `T ⊆ S`. -/
private lemma exists_submodular_weights {n : ℕ} {f : Finset (Fin n) → ℝ}
    (hf : IsSuccessFn f) (hsub : SubsamplingSM.Offline.IsSubmodular f)
    (S : Finset (Fin n)) :
    ∃ a : Fin n → ℝ,
      (∀ i ∈ S, 0 ≤ a i) ∧
      (∑ i ∈ S, a i = f S) ∧
      (∀ T ⊆ S, ∑ i ∈ T, a i ≤ f T) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 0, by simp, by simp [hf.2.1], ?_⟩
    intro T _
    simp [(hf.2.2 T).1]
  | @insert e S he ih =>
    rcases ih with ⟨a, ha_nonneg, ha_sum, ha_sub⟩
    let a' : Fin n → ℝ := Function.update a e (f (insert e S) - f S)
    have ha'_eq_e : a' e = f (insert e S) - f S := Function.update_self e (f (insert e S) - f S) a
    have ha'_ne : ∀ i : Fin n, i ≠ e → a' i = a i :=
      fun i hne => Function.update_of_ne hne (f (insert e S) - f S) a
    refine ⟨a', ?_, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with hie | hiS
      · rw [hie, ha'_eq_e]
        have := hf.1 S (insert e S) (Finset.subset_insert e S)
        linarith
      · rw [ha'_ne i (by rintro rfl; exact he hiS)]
        exact ha_nonneg i hiS
    · rw [Finset.sum_insert he, ha'_eq_e]
      have h_eq : ∑ i ∈ S, a' i = ∑ i ∈ S, a i :=
        Finset.sum_congr rfl (fun i hi => ha'_ne i (by rintro rfl; exact he hi))
      rw [h_eq, ha_sum]
      ring
    · intro T hT
      by_cases heT : e ∈ T
      · let T₀ : Finset (Fin n) := T.erase e
        have hT₀S : T₀ ⊆ S := by
          intro x hx
          rcases Finset.mem_erase.mp hx with ⟨hne, hxT⟩
          rcases Finset.mem_insert.mp (hT hxT) with hxe | hxS
          · exact absurd hxe hne
          · exact hxS
        have heT₀ : e ∉ T₀ := by simp [T₀]
        have hins : insert e T₀ = T := Finset.insert_erase heT
        have hsumT₀ : ∑ i ∈ T₀, a' i = ∑ i ∈ T₀, a i :=
          Finset.sum_congr rfl (fun i hi => ha'_ne i (Finset.mem_erase.mp hi).1)
        rw [← hins, Finset.sum_insert heT₀, ha'_eq_e, hsumT₀]
        have h1 := ha_sub T₀ hT₀S
        have h2 := hsub T₀ S e hT₀S he
        linarith
      · have hTS : T ⊆ S := by
          intro x hx
          rcases Finset.mem_insert.mp (hT hx) with hxe | hxS
          · rw [hxe] at hx
            exact absurd hx heT
          · exact hxS
        have hsumT : ∑ i ∈ T, a' i = ∑ i ∈ T, a i :=
          Finset.sum_congr rfl (fun i hi => ha'_ne i (by rintro rfl; exact heT hi))
        rw [hsumT]
        exact ha_sub T hTS

/-- Choosing the `j` largest weights in `G` yields at least a `j / |G|` fraction of `∑_{i ∈ G} x_i`. -/
private lemma exists_subset_sum_ge {α : Type*} [DecidableEq α]
    (x : α → ℝ) (j : ℕ) :
    ∀ (k : ℕ) (G : Finset α), G.card = j + k →
      ∃ J ⊆ G, J.card = j ∧ (G.card : ℝ) * (∑ i ∈ J, x i) ≥ (j : ℝ) * (∑ i ∈ G, x i) := by
  intro k
  induction k with
  | zero =>
    intro G hcard
    exact ⟨G, Finset.Subset.rfl, by omega, by rw [hcard, Nat.add_zero]⟩
  | succ k ih =>
    intro G hcard
    by_cases hj0 : j = 0
    · subst hj0
      exact ⟨∅, Finset.empty_subset G, rfl, by simp⟩
    · have hG_ne : G.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨u, huG, hu_min⟩ := Finset.exists_min_image G x hG_ne
      let G' : Finset α := G.erase u
      have hcard' : G'.card = j + k := by
        have := Finset.card_erase_of_mem huG
        dsimp [G']
        omega
      have hmin_sum : (G.card : ℝ) * x u ≤ ∑ i ∈ G, x i := by
        have := Finset.sum_le_sum (s := G) (fun i hi => hu_min i hi)
        simpa using this
      have hsplit : ∑ i ∈ G, x i = x u + ∑ i ∈ G', x i :=
        (Finset.add_sum_erase G x huG).symm
      have hcard_cast : (G.card : ℝ) = (G'.card : ℝ) + 1 := by
        rw [hcard, hcard']
        push_cast
        ring
      have hux_le : (G'.card : ℝ) * x u ≤ ∑ i ∈ G', x i := by
        have hmul_cast : (G.card : ℝ) * x u = (G'.card : ℝ) * x u + x u := by
          rw [hcard_cast]
          ring
        linarith
      have hstep : (G'.card : ℝ) * (∑ i ∈ G, x i) ≤ (G.card : ℝ) * (∑ i ∈ G', x i) := by
        calc
          (G'.card : ℝ) * (∑ i ∈ G, x i) =
              (G'.card : ℝ) * x u + (G'.card : ℝ) * (∑ i ∈ G', x i) := by
            rw [hsplit]
            ring
          _ ≤ (∑ i ∈ G', x i) + (G'.card : ℝ) * (∑ i ∈ G', x i) := by linarith
          _ = (G.card : ℝ) * (∑ i ∈ G', x i) := by
            rw [hcard_cast]
            ring
      obtain ⟨J, hJG', hJcard, hJsum⟩ := ih G' hcard'
      have hG'_pos : (0 : ℝ) < (G'.card : ℝ) := by
        have : 0 < G'.card := by omega
        exact Nat.cast_pos.mpr this
      have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hj0)
      have hG_pos : (0 : ℝ) < (G.card : ℝ) := by linarith
      refine ⟨J, Finset.Subset.trans hJG' (Finset.erase_subset u G), hJcard, ?_⟩
      have hm1 : (j : ℝ) * ((G'.card : ℝ) * (∑ i ∈ G, x i)) ≤
          (j : ℝ) * ((G.card : ℝ) * (∑ i ∈ G', x i)) :=
        mul_le_mul_of_nonneg_left hstep hj_pos.le
      have hm2 : (G.card : ℝ) * ((j : ℝ) * (∑ i ∈ G', x i)) ≤
          (G.card : ℝ) * ((G'.card : ℝ) * (∑ i ∈ J, x i)) :=
        mul_le_mul_of_nonneg_left hJsum hG_pos.le
      have hcomb : (G'.card : ℝ) * ((j : ℝ) * (∑ i ∈ G, x i)) ≤
          (G'.card : ℝ) * ((G.card : ℝ) * (∑ i ∈ J, x i)) := by
        linarith
      exact le_of_mul_le_mul_left hcomb hG'_pos

end Combinatorics

/-! ### Section 4: Pure Algebraic Inequalities for `|S| = 2` (Lemma 4.4) and `|S| ≥ 3` (Lemma 4.6) -/

section AlgebraicLemmas

private lemma lemma_4_4_alg {ρ x s p M : ℝ}
    (hρ0 : 0 < ρ) (hρ12 : ρ < 1 / 2) (hρ_prod : ρ * (2 - ρ) * (1 + ρ) = 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hp0 : 0 ≤ p) (hsp1 : s + p < 1) (hpx_s : p * x ≤ s)
    (hM1 : (1 - s) * x ≤ M) (hM2 : (1 - p) * (1 - x) ≤ M) (hM3 : 1 - 2 * p ≤ M) :
    1 - p - s ≤ (1 + ρ) * M := by
  have hs_lt1 : s < 1 := by linarith
  have hM_nonneg : 0 ≤ M := by nlinarith only [hs_lt1, hx0, hM1]
  rcases le_or_gt x ρ with hx_le | hx_gt
  · have hid : 1 - p - s = (1 - p) * (1 - x) + x * (1 - 2 * p) - (s - p * x) := by ring
    have hle1 : 1 - p - s ≤ (1 + x) * M := by nlinarith only [hid, hx0, hpx_s, hM2, hM3]
    nlinarith only [hle1, hx_le, hM_nonneg]
  · have hid : x * (2 - x) * (1 - p - s) =
        (1 - x) * ((1 - s) * x) + x * (1 - 2 * p) - x * (s - p * x) := by ring
    have hle1 : x * (2 - x) * (1 - p - s) ≤ M := by
      nlinarith only [hid, hx0, hx1, hpx_s, hM1, hM3]
    have hquad_diff : x * (2 - x) - ρ * (2 - ρ) = (x - ρ) * (2 - x - ρ) := by ring
    have hquad_ge : ρ * (2 - ρ) ≤ x * (2 - x) := by
      nlinarith only [hquad_diff, hx_gt, hx1, hρ12]
    have h1ps_nonneg : 0 ≤ 1 - p - s := by linarith
    have hle2 : ρ * (2 - ρ) * (1 - p - s) ≤ M := by
      have := mul_le_mul_of_nonneg_right hquad_ge h1ps_nonneg
      linarith
    have h1ρ_pos : 0 < 1 + ρ := by linarith
    have hmul := mul_le_mul_of_nonneg_left hle2 h1ρ_pos.le
    have hprod_id : (1 + ρ) * (ρ * (2 - ρ) * (1 - p - s)) =
        (ρ * (2 - ρ) * (1 + ρ)) * (1 - p - s) := by ring
    rw [hprod_id, hρ_prod, one_mul] at hmul
    exact hmul

private lemma lemma_4_6_alg {m : ℕ} (hm : 2 ≤ m) {θ p M : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hp0 : 0 < p)
    (hR0 : 0 < 1 - p * (1 + (m : ℝ) * θ))
    (hM : ∀ j : ℕ, j ≤ m → 0 ≤ 1 - (j + 1 : ℝ) * p →
      (1 - θ + (j : ℝ) * (θ / (m : ℝ))) * (1 - (j + 1 : ℝ) * p) ≤ M) :
    (17 / 24 : ℝ) * (1 - p * (1 + (m : ℝ) * θ)) ≤ M := by
  set R₀ : ℝ := 1 - p * (1 + (m : ℝ) * θ)
  have hm_real : (2 : ℝ) ≤ (m : ℝ) := Nat.ofNat_le_cast.mpr hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have hmθ_nonneg : 0 ≤ (m : ℝ) * θ := by positivity
  set ℓ : ℕ := ⌊(m : ℝ) * θ⌋₊
  have hℓ_le_mθ : (ℓ : ℝ) ≤ (m : ℝ) * θ := Nat.floor_le hmθ_nonneg
  have hmθ_lt_ℓ1 : (m : ℝ) * θ < (ℓ : ℝ) + 1 := Nat.lt_floor_add_one ((m : ℝ) * θ)
  have hℓ_le_m_real : (ℓ : ℝ) ≤ (m : ℝ) := by
    have : (m : ℝ) * θ ≤ (m : ℝ) * 1 := mul_le_mul_of_nonneg_left hθ1 hm_pos.le
    linarith
  have hℓ_le_m : ℓ ≤ m := Nat.cast_le.mp hℓ_le_m_real
  set a : ℝ := (m : ℝ) * θ - (ℓ : ℝ)
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  set A : ℝ := 1 - θ + θ ^ 2
  set d : ℝ := θ / (m : ℝ)
  have hmd : (m : ℝ) * d = θ := mul_div_cancel₀ θ (ne_of_gt hm_pos)
  have hd_pos : 0 < d := div_pos hθ0 hm_pos
  have h2d_le_θ : 2 * d ≤ θ := by
    have : 2 * d ≤ (m : ℝ) * d := mul_le_mul_of_nonneg_right hm_real hd_pos.le
    linarith
  have hA_gt : 17 / 24 < A := by
    have hid : A - 17 / 24 = (θ - 1 / 2) ^ 2 + 1 / 24 := by dsimp [A]; ring
    have hsq := sq_nonneg (θ - 1 / 2)
    linarith
  have hAd_ge : 7 / 16 ≤ A - d := by
    have hid : 1 - 3 * θ / 2 + θ ^ 2 = (θ - 3 / 4) ^ 2 + 7 / 16 := by ring
    have hA_def : A = 1 - θ + θ ^ 2 := rfl
    have hsq := sq_nonneg (θ - 3 / 4)
    linarith
  have hu_eq : 1 - (ℓ + 1 : ℝ) * p = R₀ + a * p := by
    dsimp [R₀, a]
    ring
  have hZℓ_eq : 1 - θ + (ℓ : ℝ) * d = A - a * d := by
    have hℓ_val : (ℓ : ℝ) = (m : ℝ) * θ - a := by dsimp [a]; ring
    calc
      1 - θ + (ℓ : ℝ) * d = 1 - θ + ((m : ℝ) * θ - a) * d := by rw [hℓ_val]
      _ = 1 - θ + θ * ((m : ℝ) * d) - a * d := by ring
      _ = A - a * d := by rw [hmd]; dsimp [A]; ring
  have hu_nonneg : 0 ≤ 1 - (ℓ + 1 : ℝ) * p := by
    rw [hu_eq]
    have : 0 ≤ a * p := mul_nonneg ha0 hp0.le
    linarith
  have h1 : (A - a * d) * (R₀ + a * p) ≤ M := by
    have h := hM ℓ hℓ_le_m hu_nonneg
    rwa [hZℓ_eq, hu_eq] at h
  rcases eq_or_lt_of_le ha0 with ha_zero | ha_pos
  · rw [← ha_zero] at h1
    simp only [zero_mul, sub_zero, add_zero] at h1
    have := mul_le_mul_of_nonneg_right hA_gt.le hR0.le
    linarith
  · have hℓ1_le_m : ℓ + 1 ≤ m := by
      by_contra hgt
      have hℓ_eq_m : ℓ = m := by omega
      have hmθ_le : (m : ℝ) * θ ≤ (ℓ : ℝ) := by
        rw [hℓ_eq_m]
        have := mul_le_mul_of_nonneg_left hθ1 hm_pos.le
        linarith
      have : a ≤ 0 := by dsimp [a]; linarith
      linarith
    have hAad_pos : 0 < A - a * d := by
      have : a * d ≤ 1 * d := mul_le_mul_of_nonneg_right ha1.le hd_pos.le
      linarith
    rcases le_or_gt 0 (R₀ - (1 - a) * p) with hv_nonneg | hv_neg
    · have hv_eq : 1 - ((ℓ + 1 : ℕ) + 1 : ℝ) * p = R₀ - (1 - a) * p := by
        push_cast
        dsimp [R₀, a]
        ring
      have hZℓ1_eq : 1 - θ + ((ℓ + 1 : ℕ) : ℝ) * d = A + (1 - a) * d := by
        push_cast
        calc
          1 - θ + ((ℓ : ℝ) + 1) * d = (1 - θ + (ℓ : ℝ) * d) + d := by ring
          _ = (A - a * d) + d := by rw [hZℓ_eq]
          _ = A + (1 - a) * d := by ring
      have hv_nonneg' : 0 ≤ 1 - ((ℓ + 1 : ℕ) + 1 : ℝ) * p := by rwa [hv_eq]
      have h2 : (A + (1 - a) * d) * (R₀ - (1 - a) * p) ≤ M := by
        have h := hM (ℓ + 1) hℓ1_le_m hv_nonneg'
        rwa [hZℓ1_eq, hv_eq] at h
      set W : ℝ := A + (1 - 2 * a) * d
      have hW_ge : 7 / 16 ≤ W := by
        have : (-1 : ℝ) * d ≤ (1 - 2 * a) * d := mul_le_mul_of_nonneg_right (by linarith) hd_pos.le
        dsimp [W]
        linarith
      have hA1ad_pos : 0 < A + (1 - a) * d := by
        have : 0 ≤ (1 - a) * d := mul_nonneg (by linarith) hd_pos.le
        linarith
      set w₁ : ℝ := (1 - a) * (A + (1 - a) * d)
      set w₂ : ℝ := a * (A - a * d)
      have hw₁_nonneg : 0 ≤ w₁ := mul_nonneg (by linarith) hA1ad_pos.le
      have hw₂_nonneg : 0 ≤ w₂ := mul_nonneg ha0 hAad_pos.le
      have hw_sum : w₁ + w₂ = W := by dsimp [w₁, w₂, W]; ring
      have hcomb_id :
          w₁ * ((A - a * d) * (R₀ + a * p)) + w₂ * ((A + (1 - a) * d) * (R₀ - (1 - a) * p)) =
          (A - a * d) * (A + (1 - a) * d) * R₀ := by
        dsimp [w₁, w₂]
        ring
      have hcomb_le : (A - a * d) * (A + (1 - a) * d) * R₀ ≤ W * M := by
        have hm1 := mul_le_mul_of_nonneg_left h1 hw₁_nonneg
        have hm2 := mul_le_mul_of_nonneg_left h2 hw₂_nonneg
        have hadd : w₁ * M + w₂ * M = W * M := by rw [← add_mul, hw_sum]
        linarith
      have hprod_id : (A - a * d) * (A + (1 - a) * d) = A * W - a * (1 - a) * d ^ 2 := by
        dsimp [W]
        ring
      have ha_quad : a * (1 - a) ≤ 1 / 4 := by nlinarith only [sq_nonneg (a - 1 / 2)]
      have hd_sq : d ^ 2 ≤ θ ^ 2 / 4 := by nlinarith only [hd_pos, h2d_le_θ]
      have ha_d_sq : a * (1 - a) * d ^ 2 ≤ θ ^ 2 / 16 := by
        have := mul_le_mul ha_quad hd_sq (sq_nonneg d) (by norm_num)
        linarith
      have hθ_ident : (A - 17 / 24) * (7 / 16) - θ ^ 2 / 16 = (3 / 8) * (θ - 7 / 12) ^ 2 := by
        dsimp [A]
        ring
      have hH_bound : (17 / 24 : ℝ) * W ≤ (A - a * d) * (A + (1 - a) * d) := by
        have h1_θ : θ ^ 2 / 16 ≤ (A - 17 / 24) * (7 / 16) := by
          linarith [hθ_ident, sq_nonneg (θ - 7 / 12)]
        have h2_W : (A - 17 / 24) * (7 / 16) ≤ (A - 17 / 24) * W :=
          mul_le_mul_of_nonneg_left hW_ge (by linarith)
        have hexp : A * W - (17 / 24 : ℝ) * W = (A - 17 / 24) * W := by ring
        linarith
      have hmul_R0 : (17 / 24 : ℝ) * W * R₀ ≤ (A - a * d) * (A + (1 - a) * d) * R₀ :=
        mul_le_mul_of_nonneg_right hH_bound hR0.le
      have hW_pos : 0 < W := by linarith
      have hfin : W * ((17 / 24 : ℝ) * R₀) ≤ W * M := by linarith
      exact le_of_mul_le_mul_left hfin hW_pos
    · have h1a_pos : 0 < 1 - a := by linarith
      have h1a_M : (A - a * d) * R₀ ≤ (1 - a) * M := by
        have hmul : (1 - a) * ((A - a * d) * (R₀ + a * p)) ≤ (1 - a) * M :=
          mul_le_mul_of_nonneg_left h1 h1a_pos.le
        have hexp : (1 - a) * (R₀ + a * p) = R₀ + a * ((1 - a) * p - R₀) := by ring
        have hpos_term : 0 ≤ a * ((1 - a) * p - R₀) := mul_nonneg ha0 (by linarith)
        have hR_le : R₀ ≤ (1 - a) * (R₀ + a * p) := by linarith
        have hmul2 := mul_le_mul_of_nonneg_left hR_le hAad_pos.le
        linarith [show (A - a * d) * ((1 - a) * (R₀ + a * p)) =
            (1 - a) * ((A - a * d) * (R₀ + a * p)) by ring]
      have hcoef_ge : (17 / 24 : ℝ) * (1 - a) ≤ A - a * d := by
        have hid : A - a * d - (17 / 24 : ℝ) * (1 - a) = (A - 17 / 24) + a * (17 / 24 - d) := by ring
        have hd_le : d ≤ 17 / 24 := by linarith
        have hpos_term : 0 ≤ a * (17 / 24 - d) := mul_nonneg ha0 (by linarith)
        linarith
      have hmul_R0 := mul_le_mul_of_nonneg_right hcoef_ge hR0.le
      have hfin : (1 - a) * ((17 / 24 : ℝ) * R₀) ≤ (1 - a) * M := by linarith
      exact le_of_mul_le_mul_left hfin h1a_pos

end AlgebraicLemmas

/-! ### Section 5: Submodular Upper Bound (`optFair f c ≤ (1 + ρ) * optND f c`) -/

section SubmodularUpperBound

private lemma card_two_ordered {n : ℕ} {S : Finset (Fin n)} (hcard : S.card = 2) (α : Fin n → ℝ) :
    ∃ a b : Fin n, a ≠ b ∧ S = {a, b} ∧ α a ≤ α b := by
  obtain ⟨u, v, huv, hSuv⟩ := Finset.card_eq_two.mp hcard
  rcases le_total (α u) (α v) with hle | hge
  · exact ⟨u, v, huv, hSuv, hle⟩
  · refine ⟨v, u, huv.symm, ?_, hge⟩
    rw [hSuv, Finset.pair_comm]

private lemma optFair_le_submodular {ρ : ℝ} (hρ_ioo : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (hρ_eq : ρ ^ 3 - ρ ^ 2 - 2 * ρ + 1 = 0)
    {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (hf : IsSuccessFn f) (hsub : SubsamplingSM.Offline.IsSubmodular f) :
    optFair f c ≤ (1 + ρ) * optND f c := by
  rcases cubic_root_props hρ_ioo hρ_eq with ⟨hρ49, hρ12, hρ_prod, hρ_24_17⟩
  have hρ_pos : 0 < ρ := hρ_ioo.1
  have hND_nonneg : 0 ≤ optND f c := optND_nonneg hf c
  unfold optFair
  refine csSup_le (nonempty_fairSet hf c) ?_
  rintro r ⟨S, α, hFair, rfl⟩
  rcases le_or_gt (rev f S α) 0 with hrev_nonpos | hrev_pos
  · nlinarith only [hrev_nonpos, hρ_pos, hND_nonneg]
  · have hfS_nonneg : 0 ≤ f S := (hf.2.2 S).1
    have hfS_pos : 0 < f S := by
      by_contra hle
      have hfS0 : f S = 0 := le_antisymm (le_of_not_gt hle) hfS_nonneg
      simp [rev, hfS0] at hrev_pos
    have hsum_lt1 : ∑ i ∈ S, α i < 1 := by
      unfold rev at hrev_pos
      nlinarith only [hrev_pos, hfS_pos]
    have hS_ne : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      rw [h0, hf.2.1] at hfS_pos
      linarith
    have hcard_pos : 0 < S.card := Finset.card_pos.mpr hS_ne
    obtain ⟨a_wt, ha_nonneg, ha_sum, ha_sub⟩ := exists_submodular_weights hf hsub S
    let x : Fin n → ℝ := fun i => a_wt i / f S
    have hx_nonneg : ∀ i ∈ S, 0 ≤ x i :=
      fun i hi => div_nonneg (ha_nonneg i hi) (le_of_lt hfS_pos)
    have hx_sum : ∑ i ∈ S, x i = 1 := by
      dsimp [x]
      rw [← Finset.sum_div, ha_sum, div_self (ne_of_gt hfS_pos)]
    have hx_sub : ∀ T ⊆ S, f S * (∑ i ∈ T, x i) ≤ f T := by
      intro T hTS
      dsimp [x]
      rw [← Finset.sum_div, mul_div_cancel₀ _ (ne_of_gt hfS_pos)]
      exact ha_sub T hTS
    have hx_swap : ∀ i ∈ S, ∀ j ∈ S, α j * (1 - x j) ≤ α i := by
      intro i hi j hj
      have h_erase_sum : ∑ k ∈ S.erase j, x k = 1 - x j := by
        have := Finset.add_sum_erase S x hj
        linarith
      have h_erase_le : f S * (1 - x j) ≤ f (S.erase j) := by
        rw [← h_erase_sum]
        exact hx_sub (S.erase j) (Finset.erase_subset j S)
      have hαj0 : 0 ≤ α j := (hFair.1 j hj).1
      have hswap := fair_swap_ineq hf hsub hFair hfS_pos hi hj
      nlinarith only [h_erase_le, hαj0, hswap, hfS_pos]
    by_cases hcard1 : S.card = 1
    · obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp hcard1
      have hND : IsNonDiscr f c {u} α := by
        refine ⟨hFair.1, hFair.2.1, ?_⟩
        intro i hi j hj
        rw [Finset.mem_singleton.mp hi, Finset.mem_singleton.mp hj]
      have hle := rev_le_optND hf hND
      nlinarith only [hle, hρ_pos, hND_nonneg]
    · by_cases hcard2 : S.card = 2
      · obtain ⟨a, b, hab, hSab, hab_le⟩ := card_two_ordered hcard2 α
        have haS : a ∈ S := by simp [hSab]
        have hbS : b ∈ S := by simp [hSab]
        set s : ℝ := α a
        set p : ℝ := α b
        have hs0 : 0 ≤ s := (hFair.1 a haS).1
        have hs1 : s ≤ 1 := (hFair.1 a haS).2
        have hp0 : 0 ≤ p := (hFair.1 b hbS).1
        have hp1 : p ≤ 1 := (hFair.1 b hbS).2
        have hsum_ab : ∑ i ∈ S, α i = s + p := by
          rw [hSab, Finset.sum_pair hab]
        have hsp1 : s + p < 1 := by linarith
        have hrev_eq : rev f S α = (1 - p - s) * f S := by
          unfold rev
          rw [hsum_ab]
          ring
        set xa : ℝ := x a
        have hxa0 : 0 ≤ xa := hx_nonneg a haS
        have hxb0 : 0 ≤ x b := hx_nonneg b hbS
        have hx_ab : xa + x b = 1 := by
          have := hx_sum
          rw [hSab, Finset.sum_pair hab] at this
          exact this
        have hxa1 : xa ≤ 1 := by linarith
        have hpx_s : p * xa ≤ s := by
          have hsw := hx_swap a haS b hbS
          have h1xb : 1 - x b = xa := by linarith
          rw [h1xb] at hsw
          exact hsw
        have hfa : f S * xa ≤ f {a} := by
          have := hx_sub {a} (Finset.singleton_subset_iff.mpr haS)
          simpa [xa] using this
        have hfb : f S * (1 - xa) ≤ f {b} := by
          have := hx_sub {b} (Finset.singleton_subset_iff.mpr hbS)
          have hxb_eq : x b = 1 - xa := by linarith
          simpa [hxb_eq] using this
        have hND1 : f S * ((1 - s) * xa) ≤ optND f c := by
          have h := uniform_subset_le_optND hf hsub hFair.2.1
            (Finset.singleton_subset_iff.mpr haS) hs0 hs1
            (fun k hk => by rw [Finset.mem_singleton.mp hk])
          simp only [Finset.card_singleton, Nat.cast_one, one_mul] at h
          nlinarith only [h, hfa, hs1]
        have hND2 : f S * ((1 - p) * (1 - xa)) ≤ optND f c := by
          have h := uniform_subset_le_optND hf hsub hFair.2.1
            (Finset.singleton_subset_iff.mpr hbS) hp0 hp1
            (fun k hk => by rw [Finset.mem_singleton.mp hk])
          simp only [Finset.card_singleton, Nat.cast_one, one_mul] at h
          nlinarith only [h, hfb, hp1]
        have hND3 : f S * (1 - 2 * p) ≤ optND f c := by
          have h := uniform_subset_le_optND hf hsub hFair.2.1 Finset.Subset.rfl hp0 hp1
            (fun k hk => by
              rw [hSab] at hk
              rcases Finset.mem_insert.mp hk with rfl | hk'
              · exact hab_le
              · rw [Finset.mem_singleton.mp hk'])
          rw [hcard2] at h
          push_cast at h
          linarith
        set M : ℝ := optND f c / f S
        have hfS_mul_M : f S * M = optND f c := mul_div_cancel₀ _ (ne_of_gt hfS_pos)
        have hM1 : (1 - s) * xa ≤ M := by nlinarith only [hND1, hfS_mul_M, hfS_pos]
        have hM2 : (1 - p) * (1 - xa) ≤ M := by nlinarith only [hND2, hfS_mul_M, hfS_pos]
        have hM3 : 1 - 2 * p ≤ M := by nlinarith only [hND3, hfS_mul_M, hfS_pos]
        have halg := lemma_4_4_alg hρ_pos hρ12 hρ_prod hxa0 hxa1 hp0 hsp1 hpx_s hM1 hM2 hM3
        rw [hrev_eq]
        calc
          (1 - p - s) * f S ≤ ((1 + ρ) * M) * f S := mul_le_mul_of_nonneg_right halg hfS_pos.le
          _ = (1 + ρ) * (f S * M) := by ring
          _ = (1 + ρ) * optND f c := by rw [hfS_mul_M]
      · -- Case `S.card ≥ 3`
        have hcard3 : 3 ≤ S.card := by omega
        set m : ℕ := S.card - 1
        have hm2 : 2 ≤ m := by omega
        obtain ⟨h, hhS, hh_max⟩ := Finset.exists_max_image S α hS_ne
        set p : ℝ := α h
        have hp0 : 0 ≤ p := (hFair.1 h hhS).1
        have hp1 : p ≤ 1 := (hFair.1 h hhS).2
        let G : Finset (Fin n) := S.erase h
        have hG_card : G.card = m := by
          dsimp [G, m]
          exact Finset.card_erase_of_mem hhS
        set θ : ℝ := 1 - x h
        have hsum_G_x : ∑ i ∈ G, x i = θ := by
          have := Finset.add_sum_erase S x hhS
          dsimp [G, θ]
          linarith
        have hxh0 : 0 ≤ x h := hx_nonneg h hhS
        have hθ0_le : 0 ≤ θ := by
          rw [← hsum_G_x]
          exact Finset.sum_nonneg (fun i hi => hx_nonneg i (Finset.erase_subset h S hi))
        have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith
        rcases eq_or_lt_of_le hp0 with hp_zero | hp_pos
        · have hND : IsNonDiscr f c S α := by
            refine ⟨hFair.1, hFair.2.1, ?_⟩
            intro i hi j hj
            have hi0 : α i = 0 := le_antisymm (le_trans (hh_max i hi) (hp_zero.symm.le)) (hFair.1 i hi).1
            have hj0 : α j = 0 := le_antisymm (le_trans (hh_max j hj) (hp_zero.symm.le)) (hFair.1 j hj).1
            rw [hi0, hj0]
          have hle := rev_le_optND hf hND
          nlinarith only [hle, hρ_pos, hND_nonneg]
        · rcases eq_or_lt_of_le hθ0_le with hθ_zero | hθ_pos
          · have hxh1 : x h = 1 := by dsimp [θ] at hθ_zero; linarith
            have hfh : f S ≤ f {h} := by
              have := hx_sub {h} (Finset.singleton_subset_iff.mpr hhS)
              simpa [hxh1] using this
            have hND_h : (1 - p) * f S ≤ optND f c := by
              have h1 := uniform_subset_le_optND hf hsub hFair.2.1
                (Finset.singleton_subset_iff.mpr hhS) hp0 hp1
                (fun k hk => by rw [Finset.mem_singleton.mp hk])
              simp only [Finset.card_singleton, Nat.cast_one, one_mul] at h1
              nlinarith only [h1, hfh, hp1]
            have hsum_ge_p : p ≤ ∑ i ∈ S, α i := by
              rw [← Finset.add_sum_erase S α hhS]
              have : 0 ≤ ∑ i ∈ S.erase h, α i :=
                Finset.sum_nonneg (fun i hi => (hFair.1 i (Finset.erase_subset h S hi)).1)
              dsimp [p]
              linarith
            unfold rev
            have hrev_le_1p : (1 - ∑ i ∈ S, α i) * f S ≤ (1 - p) * f S :=
              mul_le_mul_of_nonneg_right (by linarith) hfS_pos.le
            nlinarith only [hrev_le_1p, hND_h, hρ_pos, hND_nonneg]
          · have hG_α : (m : ℝ) * (p * θ) ≤ ∑ i ∈ G, α i := by
              have hle_each : ∀ i ∈ G, p * θ ≤ α i :=
                fun i hi => hx_swap i (Finset.erase_subset h S hi) h hhS
              have hsum := Finset.sum_le_sum hle_each
              simpa [hG_card] using hsum
            have hsum_S_α : p * (1 + (m : ℝ) * θ) ≤ ∑ i ∈ S, α i := by
              have hsplit := (Finset.add_sum_erase S α hhS).symm
              change ∑ i ∈ S, α i = p + ∑ i ∈ G, α i at hsplit
              linarith [show p * (1 + (m : ℝ) * θ) = p + (m : ℝ) * (p * θ) by ring]
            set R₀ : ℝ := 1 - p * (1 + (m : ℝ) * θ)
            have hrev_le_R0 : rev f S α ≤ R₀ * f S := by
              unfold rev
              exact mul_le_mul_of_nonneg_right (by dsimp [R₀]; linarith) hfS_pos.le
            have hR0_pos : 0 < R₀ := by nlinarith only [hrev_pos, hrev_le_R0, hfS_pos]
            set M : ℝ := optND f c / f S
            have hfS_mul_M : f S * M = optND f c := mul_div_cancel₀ _ (ne_of_gt hfS_pos)
            have hm_pos : (0 : ℝ) < (m : ℝ) := by
              have : 0 < m := by omega
              exact Nat.cast_pos.mpr this
            have hM_family : ∀ j : ℕ, j ≤ m → 0 ≤ 1 - (j + 1 : ℝ) * p →
                (1 - θ + (j : ℝ) * (θ / (m : ℝ))) * (1 - (j + 1 : ℝ) * p) ≤ M := by
              intro j hjm hj_nonneg
              obtain ⟨J, hJG, hJcard, hJsum⟩ :=
                exists_subset_sum_ge x j (m - j) G (by omega)
              rw [hG_card, hsum_G_x] at hJsum
              have hJ_div : (j : ℝ) * (θ / (m : ℝ)) ≤ ∑ i ∈ J, x i := by
                have hmul : (m : ℝ) * ((j : ℝ) * (θ / (m : ℝ))) = (j : ℝ) * θ := by
                  calc
                    (m : ℝ) * ((j : ℝ) * (θ / (m : ℝ))) = (j : ℝ) * ((m : ℝ) * (θ / (m : ℝ))) := by ring
                    _ = (j : ℝ) * θ := by rw [mul_div_cancel₀ θ (ne_of_gt hm_pos)]
                nlinarith only [hJsum, hmul, hm_pos]
              let T : Finset (Fin n) := insert h J
              have hhJ : h ∉ J := fun hhJ => by
                have := hJG hhJ
                simp [G] at this
              have hTS : T ⊆ S :=
                Finset.insert_subset_iff.mpr ⟨hhS, Finset.Subset.trans hJG (Finset.erase_subset h S)⟩
              have hTcard : (T.card : ℝ) = (j : ℝ) + 1 := by
                have hc : T.card = j + 1 := by
                  dsimp [T]
                  rw [Finset.card_eq_sum_ones, Finset.sum_insert hhJ, ← Finset.card_eq_sum_ones, hJcard]
                  omega
                rw [hc]
                push_cast
                ring
              have hfT : f S * (1 - θ + (j : ℝ) * (θ / (m : ℝ))) ≤ f T := by
                have hxT := hx_sub T hTS
                have hsumT : ∑ i ∈ T, x i = 1 - θ + ∑ i ∈ J, x i := by
                  dsimp [T, θ]
                  rw [Finset.sum_insert hhJ]
                  ring
                rw [hsumT] at hxT
                have := mul_le_mul_of_nonneg_left
                  (show 1 - θ + (j : ℝ) * (θ / (m : ℝ)) ≤ 1 - θ + ∑ i ∈ J, x i by linarith)
                  hfS_pos.le
                linarith
              have hND_T := uniform_subset_le_optND hf hsub hFair.2.1 hTS hp0 hp1
                (fun k hk => hh_max k (hTS hk))
              rw [hTcard] at hND_T
              nlinarith only [hND_T, hfT, hj_nonneg, hfS_mul_M, hfS_pos]
            have halg := lemma_4_6_alg hm2 hθ_pos hθ1 hp_pos hR0_pos hM_family
            have h17_24 : (17 / 24 : ℝ) * (R₀ * f S) ≤ optND f c := by
              nlinarith only [halg, hfS_mul_M, hfS_pos]
            have hRF_nonneg : 0 ≤ R₀ * f S := mul_nonneg hR0_pos.le hfS_pos.le
            calc
              rev f S α ≤ 1 * (R₀ * f S) := by linarith [hrev_le_R0]
              _ ≤ ((17 / 24 : ℝ) * (1 + ρ)) * (R₀ * f S) :=
                mul_le_mul_of_nonneg_right hρ_24_17.le hRF_nonneg
              _ = (1 + ρ) * ((17 / 24 : ℝ) * (R₀ * f S)) := by ring
              _ ≤ (1 + ρ) * optND f c :=
                mul_le_mul_of_nonneg_left h17_24 (by linarith [hρ_pos])

end SubmodularUpperBound

/-! ### Section 6: Tightness Instance on `Fin 2` (Lemma 4.5) -/

section TightnessInstance

private lemma fin2_eq (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

private lemma tightness_fin2 {ρ : ℝ} (hρ_ioo : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (hρ_eq : ρ ^ 3 - ρ ^ 2 - 2 * ρ + 1 = 0) :
    ∃ (n : ℕ) (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ),
      IsSuccessFn f ∧ IsAdditive f ∧ SubsamplingSM.Offline.IsSubmodular f ∧
      (∀ i, 0 ≤ c i) ∧ 0 < optFair f c ∧ optFair f c = (1 + ρ) * optND f c := by
  have hρ0 : 0 < ρ := hρ_ioo.1
  have hρ1 : ρ < 1 := hρ_ioo.2
  have h1ρ_pos : 0 < 1 + ρ := by linarith
  have h1ρ_ne : (1 + ρ : ℝ) ≠ 0 := ne_of_gt h1ρ_pos
  let w : Fin 2 → ℝ := fun i => if i = 0 then ρ else 1 - ρ
  let f : Finset (Fin 2) → ℝ := fun S => ∑ i ∈ S, w i
  let c : Fin 2 → ℝ := fun i =>
    if i = 0 then ρ ^ 3 / (1 + ρ) else ρ * (1 - ρ) / (1 + ρ)
  have hw_nonneg : ∀ i : Fin 2, 0 ≤ w i := by
    intro i
    dsimp [w]
    split_ifs <;> linarith
  have hsum_univ : ∑ i : Fin 2, w i = 1 := by
    rw [Fin.sum_univ_two]
    dsimp [w]
    norm_num
  have hAdd : IsAdditive f := by
    intro S
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [f]
  have hSub : SubsamplingSM.Offline.IsSubmodular f := isSubmodular_of_isAdditive hAdd
  have hSucc : IsSuccessFn f := by
    refine ⟨?_, by simp [f], ?_⟩
    · intro A B hAB
      exact Finset.sum_le_sum_of_subset_of_nonneg hAB (fun i _ _ => hw_nonneg i)
    · intro S
      refine ⟨Finset.sum_nonneg (fun i _ => hw_nonneg i), ?_⟩
      calc
        f S ≤ ∑ i ∈ (Finset.univ : Finset (Fin 2)), w i :=
          Finset.sum_le_univ_sum_of_nonneg hw_nonneg
        _ = 1 := hsum_univ
  have hc_nonneg : ∀ i : Fin 2, 0 ≤ c i := by
    intro i
    dsimp [c]
    split_ifs
    · exact div_nonneg (pow_nonneg hρ0.le 3) h1ρ_pos.le
    · exact div_nonneg (mul_nonneg hρ0.le (by linarith)) h1ρ_pos.le
  have hf_0 : f {0} = ρ := by simp [f, w]
  have hf_1 : f {1} = 1 - ρ := by simp [f, w]
  have hf_01 : f {0, 1} = 1 := by
    have hne : (0 : Fin 2) ≠ 1 := by decide
    rw [show f {0, 1} = w 0 + w 1 from Finset.sum_pair hne]
    dsimp [w]
    norm_num
  -- Step 1: `optND f c = (1 - ρ) / (1 + ρ)`
  have hND_ge : (1 - ρ) / (1 + ρ) ≤ optND f c := by
    let α₁ : Fin 2 → ℝ := fun _ => ρ / (1 + ρ)
    have hND₁ : IsNonDiscr f c {1} α₁ := by
      refine ⟨?_, ?_, fun _ _ _ _ => rfl⟩
      · intro i _
        dsimp [α₁]
        exact ⟨div_nonneg hρ0.le h1ρ_pos.le, (div_le_one h1ρ_pos).mpr (by linarith)⟩
      · intro i hi
        rw [Finset.mem_singleton.mp hi]
        have her : ({1} : Finset (Fin 2)).erase 1 = ∅ := by decide
        rw [her, hf_1, hSucc.2.1]
        dsimp [α₁, c]
        norm_num
        linarith [show (ρ / (1 + ρ)) * (1 - ρ) = ρ * (1 - ρ) / (1 + ρ) by ring]
    have hrev₁ : rev f {1} α₁ = (1 - ρ) / (1 + ρ) := by
      unfold rev
      rw [Finset.sum_singleton, hf_1]
      dsimp [α₁]
      field_simp [h1ρ_ne]
      ring
    rw [← hrev₁]
    exact rev_le_optND hSucc hND₁
  have hND_le : optND f c ≤ (1 - ρ) / (1 + ρ) := by
    unfold optND
    refine csSup_le (nonempty_ndSet hSucc c) ?_
    rintro r ⟨S, α, ⟨hTC, hFeas, hEq⟩, rfl⟩
    by_cases h0 : (0 : Fin 2) ∈ S <;> by_cases h1 : (1 : Fin 2) ∈ S
    · have hS : S = {0, 1} := by ext x; rcases fin2_eq x with rfl | rfl <;> simp [h0, h1]
      subst hS
      have hfeas1 := hFeas 1 h1
      have her1 : ({0, 1} : Finset (Fin 2)).erase 1 = {0} := by decide
      rw [her1, hf_01, hf_0] at hfeas1
      dsimp [c] at hfeas1
      norm_num at hfeas1
      have hα1 : ρ ≤ α 1 * (1 + ρ) := by
        have hdiv : ρ * (1 - ρ) ≤ α 1 * (1 - ρ) * (1 + ρ) :=
          (div_le_iff₀ h1ρ_pos).mp (by linarith)
        nlinarith only [hdiv, hρ1]
      have hα01 : α 0 = α 1 := hEq 0 h0 1 h1
      have hrev01 : rev f {0, 1} α = 1 - 2 * α 1 := by
        unfold rev
        rw [Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1), hf_01, hα01]
        ring
      rw [hrev01, le_div_iff₀ h1ρ_pos]
      nlinarith only [hα1]
    · have hS : S = {0} := by ext x; rcases fin2_eq x with rfl | rfl <;> simp [h0, h1]
      subst hS
      have hfeas0 := hFeas 0 h0
      have her0 : ({0} : Finset (Fin 2)).erase 0 = ∅ := by decide
      rw [her0, hf_0, hSucc.2.1] at hfeas0
      dsimp [c] at hfeas0
      simp only [mul_zero] at hfeas0
      have hα0 : ρ ^ 2 ≤ α 0 * (1 + ρ) := by
        have hdiv : ρ ^ 3 ≤ α 0 * ρ * (1 + ρ) :=
          (div_le_iff₀ h1ρ_pos).mp (by linarith)
        nlinarith only [hdiv, hρ0]
      unfold rev
      rw [Finset.sum_singleton, hf_0, le_div_iff₀ h1ρ_pos]
      nlinarith only [hα0, hρ0, hρ_eq]
    · have hS : S = {1} := by ext x; rcases fin2_eq x with rfl | rfl <;> simp [h0, h1]
      subst hS
      have hfeas1 := hFeas 1 h1
      have her1 : ({1} : Finset (Fin 2)).erase 1 = ∅ := by decide
      rw [her1, hf_1, hSucc.2.1] at hfeas1
      dsimp [c] at hfeas1
      norm_num at hfeas1
      have hα1 : ρ ≤ α 1 * (1 + ρ) := by
        have hdiv : ρ * (1 - ρ) ≤ α 1 * (1 - ρ) * (1 + ρ) :=
          (div_le_iff₀ h1ρ_pos).mp (by linarith)
        nlinarith only [hdiv, hρ1]
      unfold rev
      rw [Finset.sum_singleton, hf_1, le_div_iff₀ h1ρ_pos]
      nlinarith only [hα1, hρ1]
    · have hS : S = ∅ := by ext x; rcases fin2_eq x with rfl | rfl <;> simp [h0, h1]
      subst hS
      simp only [rev, hSucc.2.1, mul_zero]
      exact div_nonneg (by linarith) h1ρ_pos.le
  have hND_eq : optND f c = (1 - ρ) / (1 + ρ) := le_antisymm hND_le hND_ge
  -- Step 2: Exhibit fair contract on `{0, 1}` achieving `1 - ρ`
  let αF : Fin 2 → ℝ := fun i => if i = 0 then ρ ^ 2 / (1 + ρ) else ρ / (1 + ρ)
  have hFeasF : IsFeasible f c {0, 1} αF := by
    intro i _hi
    rcases fin2_eq i with rfl | rfl
    · have her0 : ({0, 1} : Finset (Fin 2)).erase 0 = {1} := by decide
      rw [her0, hf_01, hf_1]
      dsimp [αF, c]
      field_simp [h1ρ_ne]
      linarith
    · have her1 : ({0, 1} : Finset (Fin 2)).erase 1 = {0} := by decide
      rw [her1, hf_01, hf_0]
      dsimp [αF, c]
      norm_num
      field_simp [h1ρ_ne]
      linarith
  have hPNE_swap : IsPNE f c {0, 1} (αF ∘ Equiv.swap (0 : Fin 2) 1) {0} := by
    refine ⟨by decide, ?_, ?_⟩
    · intro k hk
      rw [Finset.mem_singleton.mp hk]
      have her0 : ({0} : Finset (Fin 2)).erase 0 = ∅ := by decide
      rw [her0, hf_0, hSucc.2.1]
      change αF 1 * ρ - c 0 ≥ αF 1 * 0
      dsimp [αF, c]
      norm_num
      field_simp [h1ρ_ne]
      nlinarith only [hρ0, hρ1]
    · intro k hk
      have hsdiff : ({0, 1} : Finset (Fin 2)) \ {0} = {1} := by decide
      rw [hsdiff] at hk
      rw [Finset.mem_singleton.mp hk]
      have hins : insert (1 : Fin 2) ({0} : Finset (Fin 2)) = {0, 1} := by decide
      rw [hins, hf_01, hf_0]
      change αF 0 * 1 - c 1 < αF 0 * ρ
      dsimp [αF, c]
      norm_num
      have hsq_lt : ρ ^ 2 < ρ := by nlinarith only [hρ0, hρ1]
      have hnum : ρ ^ 2 * (1 - ρ) < ρ * (1 - ρ) :=
        mul_lt_mul_of_pos_right hsq_lt (by linarith)
      have hdiv : ρ ^ 2 * (1 - ρ) / (1 + ρ) < ρ * (1 - ρ) / (1 + ρ) :=
        div_lt_div_of_pos_right hnum h1ρ_pos
      linarith [show (ρ ^ 2 / (1 + ρ)) * (1 - ρ) = ρ ^ 2 * (1 - ρ) / (1 + ρ) by ring]
  have hU0 : αF 0 * f {0, 1} - c 0 ≥ αF 1 * f {0} - c 0 := by
    rw [hf_01, hf_0]
    dsimp [αF]
    norm_num
    linarith [show ρ ^ 2 / (1 + ρ) * 1 = (ρ / (1 + ρ)) * ρ by ring]
  have hU1 : αF 1 * f {0, 1} - c 1 ≥ αF 0 * f {0} := by
    rw [hf_01, hf_0]
    dsimp [αF, c]
    norm_num
    field_simp [h1ρ_ne]
    nlinarith only [hρ0, hρ1]
  have hFairF : IsFair f c {0, 1} αF := by
    refine ⟨?_, hFeasF, ?_⟩
    · intro i _
      dsimp [αF]
      split_ifs
      · exact ⟨div_nonneg (sq_nonneg ρ) h1ρ_pos.le, (div_le_one h1ρ_pos).mpr (by nlinarith only [hρ0, hρ1])⟩
      · exact ⟨div_nonneg hρ0.le h1ρ_pos.le, (div_le_one h1ρ_pos).mpr (by linarith)⟩
    · intro i hi j hj
      rcases fin2_eq i with rfl | rfl <;> rcases fin2_eq j with rfl | rfl
      · refine ⟨{0, 1}, ?_, ?_, ?_⟩
        · simp only [Equiv.swap_self]
          exact ⟨Finset.Subset.rfl, hFeasF, fun k hk => by simp at hk⟩
        · rw [if_pos hi]
        · rw [if_pos hi]
      · refine ⟨{0}, hPNE_swap, ?_, ?_⟩
        · simp only [Finset.mem_singleton, ↓reduceIte]
          exact hU0
        · have h1not : (1 : Fin 2) ∉ ({0} : Finset (Fin 2)) := by decide
          rw [if_neg h1not]
          linarith
      · refine ⟨{0}, ?_, ?_, ?_⟩
        · rw [Equiv.swap_comm]
          exact hPNE_swap
        · have h1not : (1 : Fin 2) ∉ ({0} : Finset (Fin 2)) := by decide
          rw [if_neg h1not]
          linarith
        · simp only [Finset.mem_singleton, ↓reduceIte]
          exact hU0
      · refine ⟨{0, 1}, ?_, ?_, ?_⟩
        · simp only [Equiv.swap_self]
          exact ⟨Finset.Subset.rfl, hFeasF, fun k hk => by simp at hk⟩
        · rw [if_pos hi]
        · rw [if_pos hi]
  have hrevF : rev f {0, 1} αF = 1 - ρ := by
    unfold rev
    rw [Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1), hf_01]
    dsimp [αF]
    norm_num
    field_simp [h1ρ_ne]
    ring
  have hFair_ge : 1 - ρ ≤ optFair f c := by
    rw [← hrevF]
    exact rev_le_optFair hSucc hFairF
  have hFair_le : optFair f c ≤ 1 - ρ := by
    have hbound := optFair_le_submodular hρ_ioo hρ_eq f c hSucc hSub
    rw [hND_eq, mul_div_cancel₀ _ h1ρ_ne] at hbound
    exact hbound
  have hFair_eq : optFair f c = 1 - ρ := le_antisymm hFair_le hFair_ge
  refine ⟨2, f, c, hSucc, hAdd, hSub, hc_nonneg, ?_, ?_⟩
  · linarith
  · rw [hFair_eq, hND_eq, mul_div_cancel₀ _ h1ρ_ne]

end TightnessInstance

theorem theorem_4_1_proof :
    (∃! ρ : ℝ, ρ ∈ Set.Ioo (0 : ℝ) 1 ∧ ρ ^ 3 - ρ ^ 2 - 2 * ρ + 1 = 0) ∧
    ∀ ρ : ℝ, ρ ∈ Set.Ioo (0 : ℝ) 1 → ρ ^ 3 - ρ ^ 2 - 2 * ρ + 1 = 0 →
      (∀ (n : ℕ) (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ), IsSuccessFn f → IsAdditive f →
        (∀ i, 0 ≤ c i) → optFair f c ≤ (1 + ρ) * optND f c) ∧
      (∀ (n : ℕ) (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ), IsSuccessFn f →
        SubsamplingSM.Offline.IsSubmodular f → (∀ i, 0 ≤ c i) → optFair f c ≤ (1 + ρ) * optND f c) ∧
      (∃ (n : ℕ) (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ), IsSuccessFn f ∧ IsAdditive f ∧
        SubsamplingSM.Offline.IsSubmodular f ∧ (∀ i, 0 ≤ c i) ∧
        0 < optFair f c ∧ optFair f c = (1 + ρ) * optND f c) := by
  refine ⟨exists_unique_cubic_root, ?_⟩
  intro ρ hρ_ioo hρ_eq
  refine ⟨?_, ?_, tightness_fin2 hρ_ioo hρ_eq⟩
  · intro n f c hf hadd _hc
    exact optFair_le_submodular hρ_ioo hρ_eq f c hf (isSubmodular_of_isAdditive hadd)
  · intro n f c hf hsub _hc
    exact optFair_le_submodular hρ_ioo hρ_eq f c hf hsub

end FairTeamContracts_Proof

open FairTeamContracts

theorem solution :
    (∃! ρ : ℝ, ρ ∈ Set.Ioo (0 : ℝ) 1 ∧ ρ ^ 3 - ρ ^ 2 - 2 * ρ + 1 = 0) ∧
    ∀ ρ : ℝ, ρ ∈ Set.Ioo (0 : ℝ) 1 → ρ ^ 3 - ρ ^ 2 - 2 * ρ + 1 = 0 →
      (∀ (n : ℕ) (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ), IsSuccessFn f → IsAdditive f →
        (∀ i, 0 ≤ c i) → optFair f c ≤ (1 + ρ) * optND f c) ∧
      (∀ (n : ℕ) (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ), IsSuccessFn f →
        SubsamplingSM.Offline.IsSubmodular f → (∀ i, 0 ≤ c i) → optFair f c ≤ (1 + ρ) * optND f c) ∧
      (∃ (n : ℕ) (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ), IsSuccessFn f ∧ IsAdditive f ∧
        SubsamplingSM.Offline.IsSubmodular f ∧ (∀ i, 0 ≤ c i) ∧
        0 < optFair f c ∧ optFair f c = (1 + ρ) * optND f c) :=
  FairTeamContracts_Proof.theorem_4_1_proof
