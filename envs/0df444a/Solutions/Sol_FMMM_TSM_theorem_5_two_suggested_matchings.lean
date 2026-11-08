-- Prove2me | solution 1 for FMMM.TSM.theorem_5_two_suggested_matchings
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T19:22:49.789867+00:00
-- url     : https://prove2.me/submissions/98cc7bac-bab2-4753-bd75-c0b0a5d0e991

import Mathlib
import Definitions.Def_FMMM_TSM_unifProb
import Definitions.Def_FMMM_TSM_IsMaxTwoMatching
import Definitions.Def_FMMM_TSM_IsTSMColoring
import Definitions.Def_FMMM_TSM_tsmRun
import Definitions.Def_FMMM_TSM_realOPT
import Definitions.Def_FMMM_TSM_Copy
import Definitions.Def_FMMM_TSM_copyEdges
import Definitions.Def_FMMM_TSM_alpha
import Definitions.Def_FMMM_TSM_tightFlow
import Definitions.Def_FMMM_TSM_tightE
import Definitions.Def_FMMM_TSM_expRatio

set_option autoImplicit false

namespace FMMMProof

/-- Clause 1: with x = 1/e, alpha = 3(1-2x^2)/(4-2x) and the inequality is (4x-1)(2x-1) < 0. -/
theorem clause1 : 1 - 1 / Real.exp 1 < FMMM.TSM.alpha := by
  unfold FMMM.TSM.alpha
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have hlo : 2 < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := (1:ℝ)) one_ne_zero; linarith
  have hhi : Real.exp 1 < 4 := by
    have := Real.exp_one_lt_d9; linarith
  set E := Real.exp 1 with hE
  rw [h2]
  have hden : 0 < 4 / 3 - 2 / (3 * E) := by
    rw [sub_pos, div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  rw [lt_div_iff₀ hden]
  rw [show (1 - 1 / E) * (4 / 3 - 2 / (3 * E)) = (4 * E * E - 6 * E + 2) / (3 * (E * E)) by
        field_simp; ring,
      show 1 - 2 / (E * E) = (3 * (E * E) - 6) / (3 * (E * E)) by field_simp; ring]
  rw [div_lt_div_iff_of_pos_right (by positivity)]
  nlinarith

/-! ## C2: order-free characterization of `tsmRun` -/

section C2
variable {A J : Type} [DecidableEq A] [DecidableEq J]

/-- one step of the TSM online phase, on the arriving type `j`. -/
def stepF (blue red : Finset (A × J)) (st : (J → ℕ) × Finset A) (j : J) :
    (J → ℕ) × Finset A :=
  let cand : Finset A :=
    if st.1 j = 0 then (blue.filter (fun e => e.2 = j)).image Prod.fst
    else if st.1 j = 1 then (red.filter (fun e => e.2 = j)).image Prod.fst
    else ∅
  (Function.update st.1 j (st.1 j + 1), if cand.card = 1 then st.2 ∪ cand else st.2)

theorem tsmRun_foldl {n : ℕ} (blue red : Finset (A × J)) (ω : Fin n → J) :
    FMMM.TSM.tsmRun blue red ω =
      (((List.finRange n).map ω).foldl (stepF blue red) (fun _ => 0, ∅)).2 := by
  unfold FMMM.TSM.tsmRun; rw [List.foldl_map]; rfl

/-- the candidate set along the `X`-edge of `j`, if it is unique. -/
def bc (X : Finset (A × J)) (j : J) : Finset A :=
  if ((X.filter (fun e => e.2 = j)).image Prod.fst).card = 1 then
    (X.filter (fun e => e.2 = j)).image Prod.fst else ∅

/-- the order-free assigned set. -/
def ofList (blue red : Finset (A × J)) (L : List J) : Finset A :=
  L.toFinset.biUnion (bc blue) ∪ (L.toFinset.filter (fun j => 2 ≤ L.count j)).biUnion (bc red)

theorem mem_ofList (blue red : Finset (A × J)) (L : List J) (a : A) :
    a ∈ ofList blue red L ↔ ∃ j ∈ L, a ∈ bc blue j ∨ (2 ≤ L.count j ∧ a ∈ bc red j) := by
  unfold ofList
  simp only [Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset, Finset.mem_filter]
  constructor
  · rintro (⟨j, hj, h⟩ | ⟨j, ⟨hj, hc⟩, h⟩)
    · exact ⟨j, hj, Or.inl h⟩
    · exact ⟨j, hj, Or.inr ⟨hc, h⟩⟩
  · rintro ⟨j, hj, h | ⟨hc, h⟩⟩
    · exact Or.inl ⟨j, hj, h⟩
    · exact Or.inr ⟨j, ⟨hj, hc⟩, h⟩

theorem count_snoc (L : List J) (x j : J) :
    (L ++ [x]).count j = L.count j + if j = x then 1 else 0 := by
  rw [List.count_append]
  by_cases h : j = x
  · subst h; simp
  · simp [List.count_singleton, Ne.symm h, h]

theorem foldl_inv (blue red : Finset (A × J)) (L : List J) :
    L.foldl (stepF blue red) (fun _ => 0, ∅) = (fun j => L.count j, ofList blue red L) := by
  induction L using List.reverseRecOn with
  | nil => simp [ofList]
  | append_singleton L x ih =>
    rw [List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil]
    unfold stepF
    simp only
    refine Prod.ext ?_ ?_
    · funext j
      simp only [Function.update_apply, count_snoc]
      by_cases h : j = x
      · subst h; simp
      · simp [h]
    · simp only
      have key : ∀ a, a ∈ ofList blue red (L ++ [x]) ↔
          a ∈ ofList blue red L ∨
            (L.count x = 0 ∧ a ∈ bc blue x) ∨ (L.count x = 1 ∧ a ∈ bc red x) := by
        intro a
        rw [mem_ofList, mem_ofList]
        constructor
        · rintro ⟨j, hj, h⟩
          rw [List.mem_append, List.mem_singleton] at hj
          by_cases hjx : j = x
          · subst hjx
            rw [count_snoc] at h
            simp only [if_true] at h
            rcases Nat.lt_or_ge (L.count j) 2 with hc | hc
            · interval_cases hcj : L.count j
              · rcases h with h | ⟨h2, _⟩
                · exact Or.inr (Or.inl ⟨rfl, h⟩)
                · omega
              · rcases h with h | ⟨_, h⟩
                · exact Or.inl ⟨j, List.count_pos_iff.mp (by omega), Or.inl h⟩
                · exact Or.inr (Or.inr ⟨rfl, h⟩)
            · have hjL : j ∈ L := List.count_pos_iff.mp (by omega)
              rcases h with h | ⟨_, h⟩
              · exact Or.inl ⟨j, hjL, Or.inl h⟩
              · exact Or.inl ⟨j, hjL, Or.inr ⟨hc, h⟩⟩
          · have hjL : j ∈ L := by
              rcases hj with hj | hj
              · exact hj
              · exact absurd hj hjx
            rw [count_snoc, if_neg hjx, Nat.add_zero] at h
            exact Or.inl ⟨j, hjL, h⟩
        · rintro (⟨j, hj, h⟩ | ⟨hc, h⟩ | ⟨hc, h⟩)
          · refine ⟨j, List.mem_append_left _ hj, ?_⟩
            rw [count_snoc]
            rcases h with h | ⟨h2, h⟩
            · exact Or.inl h
            · exact Or.inr ⟨by omega, h⟩
          · exact ⟨x, List.mem_append_right _ (List.mem_singleton_self x), Or.inl h⟩
          · refine ⟨x, List.mem_append_right _ (List.mem_singleton_self x), Or.inr ⟨?_, h⟩⟩
            rw [count_snoc, if_pos rfl, hc]
      ext a
      rw [key]
      by_cases h0 : L.count x = 0
      · simp only [h0, if_true]
        unfold bc
        split_ifs <;> simp_all
      · by_cases h1 : L.count x = 1
        · simp only [h0, h1, if_true, if_false, one_ne_zero]
          unfold bc
          split_ifs <;> simp_all
        · simp only [h0, h1, if_false]
          simp

/-- **C2**: the TSM run is order-free. -/
theorem tsmRun_eq_ofList {n : ℕ} (blue red : Finset (A × J)) (ω : Fin n → J) :
    FMMM.TSM.tsmRun blue red ω = ofList blue red ((List.finRange n).map ω) := by
  rw [tsmRun_foldl, foldl_inv]

end C2

section C2b
variable {A J : Type} [DecidableEq A] [DecidableEq J]

theorem count_map_finRange {n : ℕ} (ω : Fin n → J) (j : J) :
    ((List.finRange n).map ω).count j = (Finset.univ.filter (fun t => ω t = j)).card := by
  rw [← List.ofFn_eq_map, ← Multiset.coe_count, ← Fin.univ_val_map, Multiset.count_map,
    Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr (fun t _ => eq_comm)

theorem card_bc_le (X : Finset (A × J)) (j : J) : (bc X j).card ≤ 1 := by
  unfold bc; split_ifs with h
  · exact h.le
  · simp

theorem ofList_subset (blue red : Finset (A × J)) (L L' : List J) (j0 : J)
    (h : ∀ j, j ≠ j0 → L.count j ≤ L'.count j) :
    ofList blue red L ⊆ ofList blue red L' ∪ (bc blue j0 ∪ bc red j0) := by
  intro a ha
  rw [mem_ofList] at ha
  obtain ⟨j, hj, hab⟩ := ha
  by_cases hj0 : j = j0
  · subst hj0
    rcases hab with hab | ⟨_, hab⟩
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hab)
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ hab)
  · refine Finset.mem_union_left _ ((mem_ofList _ _ _ _).2 ⟨j, ?_, ?_⟩)
    · have h1 := h j hj0
      have h2 : 0 < L.count j := List.count_pos_iff.mpr hj
      exact List.count_pos_iff.mp (by omega)
    · rcases hab with hab | ⟨hc, hab⟩
      · exact Or.inl hab
      · exact Or.inr ⟨le_trans hc (h j hj0), hab⟩

theorem card_ofList_le (blue red : Finset (A × J)) (L L' : List J) (j0 : J)
    (h : ∀ j, j ≠ j0 → L.count j ≤ L'.count j) :
    (ofList blue red L).card ≤ (ofList blue red L').card + 2 := by
  calc (ofList blue red L).card ≤ (ofList blue red L' ∪ (bc blue j0 ∪ bc red j0)).card :=
        Finset.card_le_card (ofList_subset blue red L L' j0 h)
    _ ≤ (ofList blue red L').card + ((bc blue j0).card + (bc red j0).card) :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_union_le _ _) _)
    _ ≤ _ := by have := card_bc_le blue j0; have := card_bc_le red j0; omega

/-- **C2 bounded differences**: changing one draw changes ALG by at most 2. -/
theorem card_tsmRun_le_of_eqOn {n : ℕ} (blue red : Finset (A × J)) (ω ω' : Fin n → J) (t : Fin n)
    (h : ∀ s, s ≠ t → ω s = ω' s) :
    (FMMM.TSM.tsmRun blue red ω).card ≤ (FMMM.TSM.tsmRun blue red ω').card + 2 := by
  rw [tsmRun_eq_ofList, tsmRun_eq_ofList]
  refine card_ofList_le blue red _ _ (ω t) (fun j hj => ?_)
  rw [count_map_finRange, count_map_finRange]
  refine Finset.card_le_card (fun s hs => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  have hst : s ≠ t := by rintro rfl; exact hj hs.symm
  rw [← h s hst]; exact hs

end C2b

/-! ## C3: McDiarmid (counting form, uniform draws) -/

section C3
variable {Ω : Type} [Fintype Ω]

noncomputable def avg (n : ℕ) (F : (Fin n → Ω) → ℝ) : ℝ :=
  (∑ ω, F ω) / (Fintype.card Ω : ℝ) ^ n

/-- bounded differences: changing one coordinate raises `f` by at most `L`. -/
def BD (n : ℕ) (f : (Fin n → Ω) → ℝ) (L : ℝ) : Prop :=
  ∀ (ω ω' : Fin n → Ω) (i : Fin n), (∀ s, s ≠ i → ω s = ω' s) → f ω ≤ f ω' + L

theorem hoeffding_fin [Nonempty Ω] (g : Ω → ℝ) (L : ℝ) (hL : ∀ x y, g x ≤ g y + L) (t : ℝ) :
    (∑ x, Real.exp (t * (g x - (∑ y, g y) / Fintype.card Ω))) / Fintype.card Ω ≤
      Real.exp (t ^ 2 * L ^ 2 / 8) := by
  classical
  let _ : MeasurableSpace Ω := ⊤
  have _ : MeasurableSingletonClass Ω := ⟨fun _ => trivial⟩
  set μ := (PMF.uniformOfFintype Ω).toMeasure with hμ
  have hint : ∀ f : Ω → ℝ, ∫ x, f x ∂μ = (∑ x, f x) / Fintype.card Ω := by
    intro f
    rw [hμ, PMF.integral_eq_sum]
    simp [PMF.uniformOfFintype_apply, div_eq_inv_mul, Finset.mul_sum]
  obtain ⟨x0, -, hx0⟩ := Finset.exists_min_image Finset.univ g Finset.univ_nonempty
  have hb : ∀ x, g x ∈ Set.Icc (g x0) (g x0 + L) :=
    fun x => ⟨hx0 x (Finset.mem_univ _), hL x x0⟩
  have h := (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := g)
    measurable_from_top.aemeasurable (MeasureTheory.ae_of_all _ hb)).mgf_le t
  simp only [ProbabilityTheory.mgf, hint] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  simp only [add_sub_cancel_left, NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs,
    NNReal.coe_ofNat]
  rw [div_pow, sq_abs]; ring

theorem sum_fin_succ (n : ℕ) (F : (Fin (n + 1) → Ω) → ℝ) :
    ∑ ω, F ω = ∑ x, ∑ r : Fin n → Ω, F (Fin.cons x r) := by
  rw [← (Fin.consEquiv (fun _ => Ω)).sum_comp, Fintype.sum_prod_type]; rfl

theorem card_fun_real (n : ℕ) :
    ((Finset.univ : Finset (Fin n → Ω)).card : ℝ) = (Fintype.card Ω : ℝ) ^ n := by
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]; push_cast; rfl

theorem mcdiarmid_mgf [Nonempty Ω] (L : ℝ) : ∀ (n : ℕ) (f : (Fin n → Ω) → ℝ), BD n f L →
    ∀ t : ℝ, avg n (fun ω => Real.exp (t * (f ω - avg n f))) ≤
      Real.exp (n * (t ^ 2 * L ^ 2 / 8)) := by
  intro n
  induction n with
  | zero =>
    intro f _ t
    unfold avg
    simp
  | succ n ih =>
    intro f hf t
    have hk : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
    set k : ℝ := (Fintype.card Ω : ℝ) with hkdef
    set h : Ω → ℝ := fun x => avg n (fun r => f (Fin.cons x r)) with hhdef
    have havg : avg (n + 1) f = (∑ x, h x) / k := by
      simp only [hhdef, avg]
      rw [sum_fin_succ, ← Finset.sum_div, div_div, pow_succ]
    have hfx : ∀ x, BD n (fun r => f (Fin.cons x r)) L := by
      intro x r r' i hi
      apply hf _ _ i.succ
      intro s hs
      cases s using Fin.cases with
      | zero => simp
      | succ s' =>
        simp only [Fin.cons_succ]
        exact hi s' (fun h' => hs (by rw [h']))
    have hh : ∀ x y, h x ≤ h y + L := by
      intro x y
      simp only [hhdef, avg]
      have hs : ∑ r : Fin n → Ω, f (Fin.cons x r) ≤ ∑ r : Fin n → Ω, (f (Fin.cons y r) + L) :=
        Finset.sum_le_sum fun r _ => hf _ _ 0 (fun s hs => by
          cases s using Fin.cases with
          | zero => exact absurd rfl hs
          | succ s' => simp)
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, card_fun_real] at hs
      have hkn : (0 : ℝ) < k ^ n := pow_pos hk n
      rw [div_le_iff₀ hkn, add_mul, div_mul_cancel₀ _ hkn.ne']
      linarith
    have hsplit : avg (n + 1) (fun ω => Real.exp (t * (f ω - avg (n + 1) f))) =
        (∑ x, Real.exp (t * (h x - (∑ y, h y) / k)) *
          avg n (fun r => Real.exp (t * (f (Fin.cons x r) - h x)))) / k := by
      rw [havg]
      unfold avg
      rw [sum_fin_succ, pow_succ, ← div_div, Finset.sum_div]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_div_assoc', Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit]
    calc (∑ x, Real.exp (t * (h x - (∑ y, h y) / k)) *
          avg n (fun r => Real.exp (t * (f (Fin.cons x r) - h x)))) / k
        ≤ (∑ x, Real.exp (t * (h x - (∑ y, h y) / k)) *
          Real.exp (n * (t ^ 2 * L ^ 2 / 8))) / k := by
          gcongr with x
          exact ih _ (hfx x) t
      _ = ((∑ x, Real.exp (t * (h x - (∑ y, h y) / k))) / k) *
          Real.exp (n * (t ^ 2 * L ^ 2 / 8)) := by
          rw [← Finset.sum_mul, mul_div_right_comm]
      _ ≤ Real.exp (t ^ 2 * L ^ 2 / 8) * Real.exp (n * (t ^ 2 * L ^ 2 / 8)) := by
          gcongr
          exact hoeffding_fin h L hh t
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * (t ^ 2 * L ^ 2 / 8)) := by
          rw [← Real.exp_add]; push_cast; ring_nf

end C3

section C3b
variable {Ω : Type} [Fintype Ω]

theorem tail_aux [Nonempty Ω] (n : ℕ) (hn : 0 < n) (g : (Fin n → Ω) → ℝ) (L : ℝ) (hL : 0 < L)
    (hg : BD n g L) (s : ℝ) (hs : 0 ≤ s) (lam : ℝ) (hlam : lam = 4 * s / (n * L ^ 2))
    (P : (Fin n → Ω) → Prop) [DecidablePred P] (hP : ∀ ω, P ω → lam * s ≤ lam * (g ω - avg n g)) :
    ((Finset.univ.filter P).card : ℝ) / (Fintype.card Ω : ℝ) ^ n ≤
      Real.exp (-(2 * s ^ 2 / (n * L ^ 2))) := by
  have hk : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hkn : (0 : ℝ) < (Fintype.card Ω : ℝ) ^ n := pow_pos hk n
  have hmgf := mcdiarmid_mgf L n g hg lam
  unfold avg at hmgf
  rw [div_le_iff₀ hkn] at hmgf
  have key : ((Finset.univ.filter P).card : ℝ) * Real.exp (lam * s) ≤
      ∑ ω, Real.exp (lam * (g ω - avg n g)) := by
    calc ((Finset.univ.filter P).card : ℝ) * Real.exp (lam * s)
        = ∑ ω ∈ Finset.univ.filter P, Real.exp (lam * s) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ ω ∈ Finset.univ.filter P, Real.exp (lam * (g ω - avg n g)) :=
          Finset.sum_le_sum fun ω hω => Real.exp_le_exp.2 (hP ω (Finset.mem_filter.1 hω).2)
      _ ≤ ∑ ω, Real.exp (lam * (g ω - avg n g)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => (Real.exp_pos _).le)
  have hexp : Real.exp (n * (lam ^ 2 * L ^ 2 / 8)) =
      Real.exp (-(2 * s ^ 2 / (n * L ^ 2))) * Real.exp (lam * s) := by
    rw [← Real.exp_add]; congr 1; rw [hlam]
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp; ring
  have h1 := key.trans (by unfold avg at *; exact hmgf)
  rw [hexp, mul_right_comm] at h1
  rw [div_le_iff₀ hkn]
  have := le_of_mul_le_mul_right h1 (Real.exp_pos _)
  linarith

/-- **C3 lower tail** (McDiarmid, counting form). -/
theorem mcdiarmid_lower [Nonempty Ω] (n : ℕ) (hn : 0 < n) (f : (Fin n → Ω) → ℝ) (L : ℝ)
    (hL : 0 < L) (hf : BD n f L) (s : ℝ) (hs : 0 ≤ s) :
    FMMM.TSM.unifProb Ω n (fun ω => f ω ≤ avg n f - s) ≤
      Real.exp (-(2 * s ^ 2 / (n * L ^ 2))) := by
  classical
  unfold FMMM.TSM.unifProb
  have hg : BD n (fun ω => -f ω) L := fun ω ω' i h => by
    have := hf ω' ω i (fun s hs => (h s hs).symm); linarith
  have havg : avg n (fun ω => -f ω) = -avg n f := by
    unfold avg; rw [Finset.sum_neg_distrib, neg_div]
  have hlam : (0 : ℝ) ≤ 4 * s / (n * L ^ 2) := by positivity
  convert tail_aux n hn (fun ω => -f ω) L hL hg s hs _ rfl (fun ω => f ω ≤ avg n f - s)
    (fun ω hω => by rw [havg]; exact mul_le_mul_of_nonneg_left (by linarith) hlam) using 2

/-- **C3 upper tail** (McDiarmid, counting form). -/
theorem mcdiarmid_upper [Nonempty Ω] (n : ℕ) (hn : 0 < n) (f : (Fin n → Ω) → ℝ) (L : ℝ)
    (hL : 0 < L) (hf : BD n f L) (s : ℝ) (hs : 0 ≤ s) :
    FMMM.TSM.unifProb Ω n (fun ω => avg n f + s ≤ f ω) ≤
      Real.exp (-(2 * s ^ 2 / (n * L ^ 2))) := by
  classical
  unfold FMMM.TSM.unifProb
  have hlam : (0 : ℝ) ≤ 4 * s / (n * L ^ 2) := by positivity
  convert tail_aux n hn f L hL hf s hs _ rfl (fun ω => avg n f + s ≤ f ω)
    (fun ω hω => mul_le_mul_of_nonneg_left (by linarith) hlam) using 2

end C3b

section BDs

theorem realOPT_le_succ {A I : Type} [Fintype A] [DecidableEq A] [DecidableEq I] {n : ℕ}
    (E : Finset (A × I)) (τ τ' : Fin n → I) (i : Fin n) (h : ∀ s, s ≠ i → τ s = τ' s) :
    FMMM.TSM.realOPT E τ ≤ FMMM.TSM.realOPT E τ' + 1 := by
  classical
  unfold FMMM.TSM.realOPT
  refine Finset.sup_le (fun M hM => ?_)
  obtain ⟨-, hE, hA, hD⟩ := Finset.mem_filter.1 hM
  set M' := M.filter (fun p => p.2 ≠ i)
  have hM' : M' ∈ ((Finset.univ : Finset (A × Fin n)).powerset.filter
      (fun M => (∀ p ∈ M, (p.1, τ' p.2) ∈ E) ∧
        (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p = q) ∧
        (∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q))) := by
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.subset_univ _), ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨hpM, hpi⟩ := Finset.mem_filter.1 hp
      rw [← h _ hpi]; exact hE p hpM
    · intro p hp q hq; exact hA p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1
    · intro p hp q hq; exact hD p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1
  have hle : M'.card ≤ _ := Finset.le_sup (f := Finset.card) hM'
  have h1 : (M.filter (fun p => ¬ (p.2 ≠ i))).card ≤ 1 := by
    refine Finset.card_le_one.2 (fun p hp q hq => hD p (Finset.mem_filter.1 hp).1 q
      (Finset.mem_filter.1 hq).1 ?_)
    exact (not_not.1 (Finset.mem_filter.1 hp).2).trans (not_not.1 (Finset.mem_filter.1 hq).2).symm
  have hsub : M ⊆ M' ∪ M.filter (fun p => ¬ (p.2 ≠ i)) := by
    intro p hp
    by_cases hpi : p.2 ≠ i
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hp, hpi⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hp, hpi⟩)
  have h3 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

/-- OPT has bounded differences 1. -/
theorem BD_realOPT {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (E : Finset (A × I)) (e : I → ℕ) (n : ℕ) :
    BD n (fun ω : Fin n → FMMM.TSM.Copy e =>
      (FMMM.TSM.realOPT E (fun t => (ω t).1) : ℝ)) 1 := by
  intro ω ω' i h
  have := realOPT_le_succ E (fun t => (ω t).1) (fun t => (ω' t).1) i
    (fun s hs => by rw [h s hs])
  dsimp only
  exact_mod_cast this

/-- ALG has bounded differences 2. -/
theorem BD_tsmRun {A J : Type} [DecidableEq A] [Fintype J] [DecidableEq J]
    (blue red : Finset (A × J)) (n : ℕ) :
    BD n (fun ω : Fin n → J => ((FMMM.TSM.tsmRun blue red ω).card : ℝ)) 2 := by
  intro ω ω' i h
  have := card_tsmRun_le_of_eqOn blue red ω ω' i h
  dsimp only
  exact_mod_cast this

end BDs

end FMMMProof

set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace FMMMProof
open FMMM.TSM

section C8

abbrev V4 (m : ℕ) := Fin 4 × Fin m

theorem mem_tightFlow {m : ℕ} {p : V4 m × V4 m} : p ∈ tightFlow m ↔ p.1.2 = p.2.2 ∧
    ((p.1.1 = 1 ∧ p.2.1 = 1) ∨ (p.1.1 = 2 ∧ p.2.1 = 1) ∨ (p.1.1 = 2 ∧ p.2.1 = 2) ∨
      (p.1.1 = 3 ∧ p.2.1 = 2) ∨ (p.1.1 = 3 ∧ p.2.1 = 3) ∨ (p.1.1 = 1 ∧ p.2.1 = 3)) := by
  unfold tightFlow; simp

theorem mem_tightE_cases {m : ℕ} {p : V4 m × V4 m} (hp : p ∈ tightE m) :
    (p.1.1 = 0 ∧ p.2.1 = 1) ∨ (p.1.1 = 3 ∧ p.2.1 = 0) ∨ (p ∈ tightFlow m) := by
  unfold tightE at hp
  rcases Finset.mem_union.1 hp with h | h
  · exact Or.inr (Or.inr h)
  · rcases (Finset.mem_filter.1 h).2 with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')

theorem card_tag_fst (m : ℕ) (t : Fin 4) :
    (Finset.univ.filter (fun a : V4 m => a.1 = t)).card ≤ m := by
  calc _ ≤ (Finset.univ.image (fun k : Fin m => ((t, k) : V4 m))).card := by
        apply Finset.card_le_card
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨a.2, Prod.ext ha.symm rfl⟩
    _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_image_le
    _ = m := by simp

theorem card_filter_snd_tag {m : ℕ} (F : Finset (V4 m × V4 m))
    (hdeg : ∀ j : V4 m, (F.filter (fun e => e.2 = j)).card ≤ 2) (t : Fin 4) :
    (F.filter (fun p => p.2.1 = t)).card ≤ 2 * m := by
  have hsub : F.filter (fun p => p.2.1 = t) ⊆
      (Finset.univ.filter (fun j : V4 m => j.1 = t)).biUnion
        (fun j => F.filter (fun e => e.2 = j)) := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨p.2, hp.2, hp.1, rfl⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j : V4 m => j.1 = t),
          (F.filter (fun e => e.2 = j)).card := Finset.card_biUnion_le
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j : V4 m => j.1 = t), 2 :=
        Finset.sum_le_sum (fun j _ => hdeg j)
    _ = 2 * (Finset.univ.filter (fun j : V4 m => j.1 = t)).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 2 * m := Nat.mul_le_mul_left 2 (card_tag_fst m t)

theorem card_filter_fst_tag {m : ℕ} (F : Finset (V4 m × V4 m))
    (hdeg : ∀ a : V4 m, (F.filter (fun e => e.1 = a)).card ≤ 2) (t : Fin 4) :
    (F.filter (fun p => p.1.1 = t)).card ≤ 2 * m := by
  have hsub : F.filter (fun p => p.1.1 = t) ⊆
      (Finset.univ.filter (fun j : V4 m => j.1 = t)).biUnion
        (fun j => F.filter (fun e => e.1 = j)) := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨p.1, hp.2, hp.1, rfl⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j : V4 m => j.1 = t),
          (F.filter (fun e => e.1 = j)).card := Finset.card_biUnion_le
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j : V4 m => j.1 = t), 2 :=
        Finset.sum_le_sum (fun j _ => hdeg j)
    _ = 2 * (Finset.univ.filter (fun j : V4 m => j.1 = t)).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 2 * m := Nat.mul_le_mul_left 2 (card_tag_fst m t)

theorem card_filter_diag {m : ℕ} (F : Finset (V4 m × V4 m)) (hF : F ⊆ tightE m) (s t : Fin 4)
    (hst : ¬ (s = 0 ∧ t = 1) ∧ ¬ (s = 3 ∧ t = 0)) :
    (F.filter (fun p => p.1.1 = s ∧ p.2.1 = t)).card ≤ m := by
  have key : ∀ r : V4 m × V4 m, r ∈ F → r.1.1 = s → r.2.1 = t → r.1.2 = r.2.2 := by
    intro r hr h1 h2
    rcases mem_tightE_cases (hF hr) with h | h | h
    · exact (hst.1 ⟨h1.symm.trans h.1, h2.symm.trans h.2⟩).elim
    · exact (hst.2 ⟨h1.symm.trans h.1, h2.symm.trans h.2⟩).elim
    · exact (mem_tightFlow.1 h).1
  have hinj : Set.InjOn (fun p : V4 m × V4 m => p.1.2)
      (F.filter (fun p => p.1.1 = s ∧ p.2.1 = t) : Set (V4 m × V4 m)) := by
    intro p hp q hq hpq
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
    have hpq' : p.1.2 = q.1.2 := hpq
    have kp := key p hp.1 hp.2.1 hp.2.2
    have kq := key q hq.1 hq.2.1 hq.2.2
    exact Prod.ext (Prod.ext (hp.2.1.trans hq.2.1.symm) hpq')
      (Prod.ext (hp.2.2.trans hq.2.2.symm) (kp.symm.trans (hpq'.trans kq)))
  calc _ ≤ (Finset.univ : Finset (Fin m)).card :=
        Finset.card_le_card_of_injOn (fun p : V4 m × V4 m => p.1.2) (fun p _ => by simp) hinj
    _ = m := by simp

theorem card_le_of_two_matching {m : ℕ} (F : Finset (V4 m × V4 m))
    (hF : IsTwoMatching (tightE m) F) : F.card ≤ 6 * m := by
  obtain ⟨hsub, hA, hJ⟩ := hF
  have hcov : F ⊆ F.filter (fun p => p.2.1 = 1) ∪ F.filter (fun p => p.1.1 = 1 ∧ p.2.1 = 3) ∪
      F.filter (fun p => p.1.1 = 2 ∧ p.2.1 = 2) ∪ F.filter (fun p => p.1.1 = 3) := by
    intro p hp
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases mem_tightE_cases (hsub hp) with h | h | h
    · tauto
    · tauto
    · rcases (mem_tightFlow.1 h).2 with h | h | h | h | h | h <;> tauto
  have h1 := card_filter_snd_tag F hJ 1
  have h2 := card_filter_diag F hsub 1 3 (by decide)
  have h3 := card_filter_diag F hsub 2 2 (by decide)
  have h4 := card_filter_fst_tag F hA 3
  have e0 := Finset.card_le_card hcov
  have e1 := Finset.card_union_le (F.filter (fun p => p.2.1 = 1) ∪
    F.filter (fun p => p.1.1 = 1 ∧ p.2.1 = 3) ∪ F.filter (fun p => p.1.1 = 2 ∧ p.2.1 = 2))
    (F.filter (fun p => p.1.1 = 3))
  have e2 := Finset.card_union_le (F.filter (fun p => p.2.1 = 1) ∪
    F.filter (fun p => p.1.1 = 1 ∧ p.2.1 = 3)) (F.filter (fun p => p.1.1 = 2 ∧ p.2.1 = 2))
  have e3 := Finset.card_union_le (F.filter (fun p => p.2.1 = 1))
    (F.filter (fun p => p.1.1 = 1 ∧ p.2.1 = 3))
  omega

def P6 : Fin 6 → Fin 4 × Fin 4 := ![(1, 1), (2, 1), (2, 2), (3, 2), (3, 3), (1, 3)]

theorem P6_inj : ∀ a b : Fin 6, P6 a = P6 b → a = b := by decide

theorem P6_tags : ∀ r : Fin 6,
    ((P6 r).1 = 1 ∧ (P6 r).2 = 1) ∨ ((P6 r).1 = 2 ∧ (P6 r).2 = 1) ∨
      ((P6 r).1 = 2 ∧ (P6 r).2 = 2) ∨ ((P6 r).1 = 3 ∧ (P6 r).2 = 2) ∨
      ((P6 r).1 = 3 ∧ (P6 r).2 = 3) ∨ ((P6 r).1 = 1 ∧ (P6 r).2 = 3) := by decide

theorem six_le_card_tightFlow (m : ℕ) : 6 * m ≤ (tightFlow m).card := by
  let φ : Fin 6 × Fin m → V4 m × V4 m := fun rk => (((P6 rk.1).1, rk.2), ((P6 rk.1).2, rk.2))
  have hinj : Function.Injective φ := by
    intro x y hxy
    have h1 : (P6 x.1).1 = (P6 y.1).1 := congrArg (fun p : V4 m × V4 m => p.1.1) hxy
    have h2 : x.2 = y.2 := congrArg (fun p : V4 m × V4 m => p.1.2) hxy
    have h3 : (P6 x.1).2 = (P6 y.1).2 := congrArg (fun p : V4 m × V4 m => p.2.1) hxy
    exact Prod.ext (P6_inj _ _ (Prod.ext h1 h3)) h2
  have hsub : Finset.univ.image φ ⊆ tightFlow m := by
    intro p hp
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨⟨r, k⟩, rfl⟩ := hp
    rw [mem_tightFlow]
    exact ⟨rfl, P6_tags r⟩
  calc 6 * m = (Finset.univ.image φ).card := by
        rw [Finset.card_image_of_injective _ hinj]; simp
    _ ≤ _ := Finset.card_le_card hsub

def fA (t : Fin 4) : Fin 4 := if t = 3 then 2 else if t = 0 then 0 else 1
def gA (t : Fin 4) : Fin 4 := if t = 0 then 0 else if t = 2 then 2 else 3
def gT (t : Fin 4) : Fin 4 := if t = 0 then 0 else if t = 1 then 2 else if t = 2 then 3 else 1

theorem tagA : ∀ τ σ : Fin 4,
    ((τ = 1 ∧ σ = 1) ∨ (τ = 2 ∧ σ = 1) ∨ (τ = 2 ∧ σ = 2) ∨
      (τ = 3 ∧ σ = 2) ∨ (τ = 3 ∧ σ = 3) ∨ (τ = 1 ∧ σ = 3)) → σ = fA τ ∨ σ = gA τ := by
  decide

theorem tagT : ∀ τ σ : Fin 4,
    ((τ = 1 ∧ σ = 1) ∨ (τ = 2 ∧ σ = 1) ∨ (τ = 2 ∧ σ = 2) ∨
      (τ = 3 ∧ σ = 2) ∨ (τ = 3 ∧ σ = 3) ∨ (τ = 1 ∧ σ = 3)) → τ = σ ∨ τ = gT σ := by
  decide

theorem card_le_two_of_sub {α : Type} [DecidableEq α] (S : Finset α) (x y : α)
    (h : ∀ p ∈ S, p = x ∨ p = y) : S.card ≤ 2 := by
  have hs : S ⊆ {x, y} := by
    intro p hp
    rcases h p hp with h | h
    · exact Finset.mem_insert.2 (Or.inl h)
    · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 h))
  calc S.card ≤ ({x, y} : Finset α).card := Finset.card_le_card hs
    _ ≤ ({y} : Finset α).card + 1 := Finset.card_insert_le _ _
    _ = 2 := by rw [Finset.card_singleton]

theorem tightFlow_deg_ad (m : ℕ) (a : V4 m) :
    ((tightFlow m).filter (fun e => e.1 = a)).card ≤ 2 := by
  apply card_le_two_of_sub _ (a, (fA a.1, a.2)) (a, (gA a.1, a.2))
  intro p hp
  rw [Finset.mem_filter, mem_tightFlow] at hp
  obtain ⟨⟨hk, ht⟩, hpa⟩ := hp
  subst hpa
  rcases tagA _ _ ht with h | h
  · exact Or.inl (Prod.ext rfl (Prod.ext h hk.symm))
  · exact Or.inr (Prod.ext rfl (Prod.ext h hk.symm))

theorem tightFlow_deg_type (m : ℕ) (j : V4 m) :
    ((tightFlow m).filter (fun e => e.2 = j)).card ≤ 2 := by
  apply card_le_two_of_sub _ ((j.1, j.2), j) ((gT j.1, j.2), j)
  intro p hp
  rw [Finset.mem_filter, mem_tightFlow] at hp
  obtain ⟨⟨hk, ht⟩, hpj⟩ := hp
  subst hpj
  rcases tagT _ _ ht with h | h
  · exact Or.inl (Prod.ext (Prod.ext h hk) rfl)
  · exact Or.inr (Prod.ext (Prod.ext h hk) rfl)

/-- C8: the 6-cycle flow is a maximum 2-matching of the tight instance. -/
theorem tight_isMax (m : ℕ) : IsMaxTwoMatching (tightE m) (tightFlow m) := by
  refine ⟨⟨?_, tightFlow_deg_ad m, tightFlow_deg_type m⟩, fun F' hF' =>
    (card_le_of_two_matching F' hF').trans (six_le_card_tightFlow m)⟩
  unfold tightE
  exact Finset.subset_union_left

end C8

section C9col
variable {A J : Type} [DecidableEq A] [DecidableEq J]

theorem pieceEdge_some {p : List (A ⊕ J)} {i : ℕ} {a : A} {j : J}
    (h : pieceEdge p i = some (a, j)) :
    (p[i]? = some (Sum.inl a) ∧ p[i+1]? = some (Sum.inr j)) ∨
      (p[i]? = some (Sum.inr j) ∧ p[i+1]? = some (Sum.inl a)) := by
  revert h
  unfold pieceEdge
  rcases p[i]? with _ | (x | x) <;> rcases p[i+1]? with _ | (y | y) <;> simp_all

theorem getE {α : Type} {l : List α} {n : ℕ} {v : α} (h : l[n]? = some v) :
    ∃ hn : n < l.length, l[n] = v := List.getElem?_eq_some_iff.1 h

theorem side_alt (p : List (A ⊕ J))
    (hadj : ∀ i : ℕ, i + 1 < p.length → ∃ e, pieceEdge p i = some e) (h0 : 0 < p.length) :
    ∀ i (hi : i < p.length), ((p[i]).isLeft = (p[0]).isLeft ↔ Even i) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have ih' := ih (by omega)
    obtain ⟨⟨a, j⟩, he⟩ := hadj i hi
    have hflip : (p[i+1]).isLeft = !(p[i]).isLeft := by
      rcases pieceEdge_some he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨_, e1⟩ := getE h1
        obtain ⟨_, e2⟩ := getE h2
        rw [e1, e2]; rfl
      · obtain ⟨_, e1⟩ := getE h1
        obtain ⟨_, e2⟩ := getE h2
        rw [e1, e2]; rfl
    rw [hflip, Nat.even_add_one, ← ih']
    cases (p[i]).isLeft <;> cases (p[0]).isLeft <;> simp

theorem pos_cases (p : List (A ⊕ J)) (hlen : 5 ≤ p.length) (hhl : p.head? = p.getLast?)
    (hdl : p.dropLast.Nodup) (s t : ℕ) (hs : s < p.length) (ht : t < p.length)
    (hst : p[s] = p[t]) :
    s = t ∨ (s = 0 ∧ t = p.length - 1) ∨ (s = p.length - 1 ∧ t = 0) := by
  have hdl_len : p.dropLast.length = p.length - 1 := List.length_dropLast
  have ND : ∀ x y (hx : x < p.length - 1) (hy : y < p.length - 1), p[x] = p[y] → x = y := by
    intro x y hx hy hxy
    have h1 : p.dropLast[x]'(by omega) = p.dropLast[y]'(by omega) := by
      rw [List.getElem_dropLast, List.getElem_dropLast]; exact hxy
    exact (List.Nodup.getElem_inj_iff hdl).1 h1
  have E0 : p[0] = p[p.length - 1] := by
    have h1 : p[0]? = p[p.length - 1]? := by
      rw [← List.head?_eq_getElem?, ← List.getLast?_eq_getElem?]; exact hhl
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
    exact Option.some.inj h1
  by_cases hs' : s = p.length - 1
  · by_cases ht' : t = p.length - 1
    · left; omega
    · right; right; refine ⟨hs', ?_⟩
      have : p[0] = p[t] := by rw [E0]; subst hs'; exact hst
      exact (ND 0 t (by omega) (by omega) this).symm
  · by_cases ht' : t = p.length - 1
    · right; left; refine ⟨?_, ht'⟩
      have : p[s] = p[0] := by rw [E0]; subst ht'; exact hst
      exact ND s 0 (by omega) (by omega) this
    · left; exact ND s t (by omega) (by omega) hst

theorem mem_of_pieceEdge' {p : List (A ⊕ J)} {i : ℕ} {a : A} {j : J}
    (h : pieceEdge p i = some (a, j)) : i + 1 < p.length := by
  rcases pieceEdge_some h with ⟨-, h2⟩ | ⟨-, h2⟩
  · exact (getE h2).1
  · exact (getE h2).1

theorem not_both_blue {F blue : Finset (A × J)} (hcol : IsTSMColoring F blue)
    (hdeg1 : ∀ v : A ⊕ J, Sum.elim (fun a => (F.filter (fun e => e.1 = a)).card)
      (fun j => (F.filter (fun e => e.2 = j)).card) v ≠ 1)
    {a : A} {j1 j2 : J} (hne : j1 ≠ j2) (h1 : (a, j1) ∈ blue) (h2 : (a, j2) ∈ blue) : False := by
  obtain ⟨hsub, pieces, hdisj, hcov, hpc⟩ := hcol
  obtain ⟨p, hp, i, hi⟩ := hcov _ (hsub h1)
  obtain ⟨q, hq, i', hi'⟩ := hcov _ (hsub h2)
  have memA : ∀ (r : List (A ⊕ J)) (k : ℕ) (jj : J), pieceEdge r k = some (a, jj) →
      Sum.inl a ∈ r := by
    intro r k jj h
    rcases pieceEdge_some h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact List.mem_iff_getElem?.2 ⟨_, h1⟩
    · exact List.mem_iff_getElem?.2 ⟨_, h2⟩
  have hpq : p = q := by
    by_contra hpq
    haveI : Std.Symm (fun p q : List (A ⊕ J) => ∀ v ∈ p, v ∉ q) :=
      ⟨fun x y h v hv hvx => h v hvx hv⟩
    exact List.Pairwise.forall hdisj hp hq hpq _ (memA p i j1 hi) (memA q i' j2 hi')
  subst hpq
  obtain ⟨hadj, hshape, hblue⟩ := hpc p hp
  rcases hshape with ⟨-, hlen, hhead, -⟩ | ⟨hlen, hhl, hdl⟩
  · cases p with
    | nil => simp at hlen
    | cons v t => exact hdeg1 v (hhead v rfl)
  · have hnn : ¬ p.Nodup := by
      intro hnd
      have h1 : p[0]? = p[p.length - 1]? := by
        rw [← List.head?_eq_getElem?, ← List.getLast?_eq_getElem?]; exact hhl
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
      have := (List.Nodup.getElem_inj_iff hnd).1 (Option.some.inj h1)
      omega
    have hev : ∀ (k : ℕ) (jj : J), pieceEdge p k = some (a, jj) → (a, jj) ∈ blue → Even k := by
      intro k jj hk hb
      rcases (hblue k _ hk).1 hb with ⟨⟨hnd, -⟩, -⟩ | ⟨-, he⟩
      · exact absurd hnd hnn
      · exact he
    have ei := hev i j1 hi h1
    have ei' := hev i' j2 hi' h2
    have hii : i ≠ i' := by
      rintro rfl
      rw [hi] at hi'
      exact hne (congrArg Prod.snd (Option.some.inj hi'))
    have hadj' : ∀ k : ℕ, k + 1 < p.length → ∃ e, pieceEdge p k = some e := by
      intro k hk
      obtain ⟨e, -, he⟩ := hadj k hk
      exact ⟨e, he⟩
    have E0 : p[0]'(by omega) = p[p.length - 1]'(by omega) := by
      have h1 : p[0]? = p[p.length - 1]? := by
        rw [← List.head?_eq_getElem?, ← List.getLast?_eq_getElem?]; exact hhl
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
      exact Option.some.inj h1
    have hk : Even (p.length - 1) := by
      have := side_alt p hadj' (by omega) (p.length - 1) (by omega)
      rw [← E0] at this
      exact this.1 rfl
    have posA : ∀ (k : ℕ) (jj : J), pieceEdge p k = some (a, jj) →
        ∃ s, (s = k ∨ s = k + 1) ∧ ∃ hs : s < p.length, p[s] = Sum.inl a := by
      intro k jj h
      rcases pieceEdge_some h with ⟨h1, _⟩ | ⟨_, h2⟩
      · obtain ⟨hs, e⟩ := getE h1
        exact ⟨k, Or.inl rfl, hs, e⟩
      · obtain ⟨hs, e⟩ := getE h2
        exact ⟨k + 1, Or.inr rfl, hs, e⟩
    obtain ⟨s, hs, hsl, es⟩ := posA i j1 hi
    obtain ⟨s', hs', hsl', es'⟩ := posA i' j2 hi'
    have hl1 := mem_of_pieceEdge' hi
    have hl2 := mem_of_pieceEdge' hi'
    have hc := pos_cases p hlen hhl hdl s s' hsl hsl' (es.trans es'.symm)
    obtain ⟨r1, hr1⟩ := ei
    obtain ⟨r2, hr2⟩ := ei'
    obtain ⟨r3, hr3⟩ := hk
    omega

end C9col

section C9alg

abbrev tg (τ σ : Fin 4) : Prop :=
  (τ = 1 ∧ σ = 1) ∨ (τ = 2 ∧ σ = 1) ∨ (τ = 2 ∧ σ = 2) ∨
    (τ = 3 ∧ σ = 2) ∨ (τ = 3 ∧ σ = 3) ∨ (τ = 1 ∧ σ = 3)

theorem tags_ne0 : ∀ τ σ : Fin 4, tg τ σ → τ ≠ 0 ∧ σ ≠ 0 := by decide

theorem tight_tags_ne : ∀ τ : Fin 4, τ ≠ 0 → tg τ (fA τ) ∧ tg τ (gA τ) ∧ fA τ ≠ gA τ := by decide

theorem tight_tagsT_ne : ∀ σ : Fin 4, σ ≠ 0 → tg σ σ ∧ tg (gT σ) σ ∧ σ ≠ gT σ := by decide

theorem mem_bc {A J : Type} [DecidableEq A] [DecidableEq J] {X : Finset (A × J)} {j : J} {a : A}
    (h : a ∈ bc X j) : (a, j) ∈ X := by
  unfold bc at h
  split_ifs at h with hc
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
    rw [Finset.mem_filter] at he
    rw [← he.2]; exact he.1
  · simp at h

theorem alg_mem {A J : Type} [DecidableEq A] [DecidableEq J] {n : ℕ} {blue red : Finset (A × J)}
    {ω : Fin n → J} {a : A} (h : a ∈ tsmRun blue red ω) :
    ∃ j, ((a, j) ∈ blue ∧ 1 ≤ (Finset.univ.filter (fun t => ω t = j)).card) ∨
      ((a, j) ∈ red ∧ 2 ≤ (Finset.univ.filter (fun t => ω t = j)).card) := by
  rw [tsmRun_eq_ofList, mem_ofList] at h
  obtain ⟨j, hj, h | ⟨hc, h⟩⟩ := h
  · refine ⟨j, Or.inl ⟨mem_bc h, ?_⟩⟩
    rw [← count_map_finRange]; exact List.count_pos_iff.2 hj
  · exact ⟨j, Or.inr ⟨mem_bc h, by rw [← count_map_finRange]; exact hc⟩⟩

theorem tight_deg_ne_one (m : ℕ) (v : V4 m ⊕ V4 m) :
    Sum.elim (fun a => ((tightFlow m).filter (fun e => e.1 = a)).card)
      (fun j => ((tightFlow m).filter (fun e => e.2 = j)).card) v ≠ 1 := by
  rcases v with a | j
  · simp only [Sum.elim_inl]
    intro h
    obtain ⟨e, he⟩ := Finset.card_eq_one.1 h
    have hmem : e ∈ (tightFlow m).filter (fun e => e.1 = a) := by
      rw [he]; exact Finset.mem_singleton_self e
    rw [Finset.mem_filter, mem_tightFlow] at hmem
    obtain ⟨⟨-, ht⟩, hea⟩ := hmem
    have hτ : a.1 ≠ 0 := by rw [← hea]; exact (tags_ne0 _ _ ht).1
    obtain ⟨h1, h2, h3⟩ := tight_tags_ne a.1 hτ
    have m1 : (a, (fA a.1, a.2)) ∈ (tightFlow m).filter (fun e => e.1 = a) := by
      rw [Finset.mem_filter, mem_tightFlow]; exact ⟨⟨rfl, h1⟩, rfl⟩
    have m2 : (a, (gA a.1, a.2)) ∈ (tightFlow m).filter (fun e => e.1 = a) := by
      rw [Finset.mem_filter, mem_tightFlow]; exact ⟨⟨rfl, h2⟩, rfl⟩
    rw [he, Finset.mem_singleton] at m1 m2
    exact h3 (congrArg (fun p : V4 m × V4 m => p.2.1) (m1.trans m2.symm))
  · simp only [Sum.elim_inr]
    intro h
    obtain ⟨e, he⟩ := Finset.card_eq_one.1 h
    have hmem : e ∈ (tightFlow m).filter (fun e => e.2 = j) := by
      rw [he]; exact Finset.mem_singleton_self e
    rw [Finset.mem_filter, mem_tightFlow] at hmem
    obtain ⟨⟨-, ht⟩, hej⟩ := hmem
    have hσ : j.1 ≠ 0 := by rw [← hej]; exact (tags_ne0 _ _ ht).2
    obtain ⟨h1, h2, h3⟩ := tight_tagsT_ne j.1 hσ
    have m1 : ((j.1, j.2), j) ∈ (tightFlow m).filter (fun e => e.2 = j) := by
      rw [Finset.mem_filter, mem_tightFlow]; exact ⟨⟨rfl, h1⟩, rfl⟩
    have m2 : ((gT j.1, j.2), j) ∈ (tightFlow m).filter (fun e => e.2 = j) := by
      rw [Finset.mem_filter, mem_tightFlow]; exact ⟨⟨rfl, h2⟩, rfl⟩
    rw [he, Finset.mem_singleton] at m1 m2
    exact h3 (congrArg (fun p : V4 m × V4 m => p.1.1) (m1.trans m2.symm))

theorem tight_not_both_blue {m : ℕ} {blue : Finset (V4 m × V4 m)}
    (hcol : IsTSMColoring (tightFlow m) blue) (a : V4 m) (ha : a.1 ≠ 0) :
    ¬ ((a, (fA a.1, a.2)) ∈ blue ∧ (a, (gA a.1, a.2)) ∈ blue) := by
  rintro ⟨h1, h2⟩
  have hne : ((fA a.1, a.2) : V4 m) ≠ (gA a.1, a.2) := fun h =>
    (tight_tags_ne a.1 ha).2.2 (congrArg Prod.fst h)
  exact not_both_blue hcol (tight_deg_ne_one m) hne h1 h2

/-- the two flow neighbours of an ad, as (blue-first, other). -/
noncomputable def bAd {m : ℕ} (blue : Finset (V4 m × V4 m)) (a : V4 m) : V4 m :=
  if (a, ((fA a.1, a.2) : V4 m)) ∈ blue then (fA a.1, a.2) else (gA a.1, a.2)

noncomputable def rAd {m : ℕ} (blue : Finset (V4 m × V4 m)) (a : V4 m) : V4 m :=
  if (a, ((fA a.1, a.2) : V4 m)) ∈ blue then (gA a.1, a.2) else (fA a.1, a.2)

theorem bAd_ne_rAd {m : ℕ} (blue : Finset (V4 m × V4 m)) (a : V4 m) (ha : a.1 ≠ 0) :
    bAd blue a ≠ rAd blue a := by
  have h3 := (tight_tags_ne a.1 ha).2.2
  unfold bAd rAd
  split_ifs
  · exact fun h => h3 (congrArg Prod.fst h)
  · exact fun h => h3 (congrArg Prod.fst h).symm

theorem tight_unassigned {m n : ℕ} {blue : Finset (V4 m × V4 m)}
    (hcol : IsTSMColoring (tightFlow m) blue) (ω : Fin n → V4 m) (a : V4 m)
    (h0 : (Finset.univ.filter (fun t => ω t = bAd blue a)).card = 0)
    (h1 : (Finset.univ.filter (fun t => ω t = rAd blue a)).card ≤ 1) :
    a ∉ tsmRun blue (tightFlow m \ blue) ω := by
  intro hA
  obtain ⟨j, hj⟩ := alg_mem hA
  have hF : (a, j) ∈ tightFlow m := by
    rcases hj with ⟨hb, -⟩ | ⟨hr, -⟩
    · exact hcol.1 hb
    · exact (Finset.mem_sdiff.1 hr).1
  rw [mem_tightFlow] at hF
  obtain ⟨hk, ht⟩ := hF
  have ha : a.1 ≠ 0 := (tags_ne0 _ _ ht).1
  have hnb := tight_not_both_blue hcol a ha
  have hj2 : j = (fA a.1, a.2) ∨ j = (gA a.1, a.2) := by
    rcases tagA _ _ ht with h | h
    · exact Or.inl (Prod.ext h hk.symm)
    · exact Or.inr (Prod.ext h hk.symm)
  unfold bAd at h0
  unfold rAd at h1
  by_cases hb : (a, ((fA a.1, a.2) : V4 m)) ∈ blue
  · rw [if_pos hb] at h0 h1
    have hr : (a, ((gA a.1, a.2) : V4 m)) ∉ blue := fun h => hnb ⟨hb, h⟩
    rcases hj2 with rfl | rfl <;> rcases hj with ⟨hb', hc⟩ | ⟨hr', hc⟩ <;> first
      | omega | exact hr hb'
  · rw [if_neg hb] at h0 h1
    rcases hj2 with rfl | rfl <;> rcases hj with ⟨hb', hc⟩ | ⟨hr', hc⟩ <;> first
      | omega | exact hb hb'

end C9alg

section C9count

theorem card_good_ge {J : Type} [Fintype J] [DecidableEq J] (N : ℕ) (b r : J) (hbr : b ≠ r) :
    (Fintype.card J - 2) ^ N + N * (Fintype.card J - 2) ^ (N - 1) ≤
      (Finset.univ.filter (fun ω : Fin N → J =>
        (Finset.univ.filter (fun t => ω t = b)).card = 0 ∧
          (Finset.univ.filter (fun t => ω t = r)).card ≤ 1)).card := by
  set C : Finset J := Finset.univ \ {b, r} with hC
  have hCc : C.card = Fintype.card J - 2 := by
    rw [hC, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Finset.card_pair hbr]
  have memC : ∀ x, x ∈ C ↔ x ≠ b ∧ x ≠ r := by
    intro x; simp [hC, not_or]
  let S0 : Finset (Fin N → J) := Fintype.piFinset (fun _ => C)
  let St : Fin N → Finset (Fin N → J) := fun t =>
    Fintype.piFinset (fun s => if s = t then ({r} : Finset J) else C)
  have hS0 : S0.card = (Fintype.card J - 2) ^ N := by
    simp only [S0, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      hCc]
  have hSt : ∀ t, (St t).card = (Fintype.card J - 2) ^ (N - 1) := by
    intro t
    simp only [St, Fintype.card_piFinset]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t), if_pos rfl,
      Finset.card_singleton, one_mul,
      Finset.prod_congr rfl (fun s hs => by rw [if_neg (Finset.ne_of_mem_erase hs)]),
      Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ,
      Fintype.card_fin, hCc]
  have hdisj1 : Disjoint S0 (Finset.univ.biUnion St) := by
    rw [Finset.disjoint_left]
    intro ω h0 h1
    obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.1 h1
    have a0 := (Fintype.mem_piFinset.1 h0) t
    have a1 := (Fintype.mem_piFinset.1 ht) t
    rw [if_pos rfl, Finset.mem_singleton] at a1
    exact ((memC _).1 a0).2 a1
  have hdisj2 : (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint St := by
    intro t _ t' _ htt'
    rw [Function.onFun, Finset.disjoint_left]
    intro ω h0 h1
    have a0 := (Fintype.mem_piFinset.1 h0) t
    have a1 := (Fintype.mem_piFinset.1 h1) t
    rw [if_pos rfl, Finset.mem_singleton] at a0
    rw [if_neg htt'] at a1
    exact ((memC _).1 a1).2 a0
  have hsub : S0 ∪ Finset.univ.biUnion St ⊆ Finset.univ.filter (fun ω : Fin N → J =>
        (Finset.univ.filter (fun t => ω t = b)).card = 0 ∧
          (Finset.univ.filter (fun t => ω t = r)).card ≤ 1) := by
    intro ω hω
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.1 hω with h0 | h1
    · have a0 := Fintype.mem_piFinset.1 h0
      constructor
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro t _; exact ((memC _).1 (a0 t)).1
      · rw [Finset.card_le_one]
        intro x hx; exact absurd (Finset.mem_filter.1 hx).2 ((memC _).1 (a0 x)).2
    · obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.1 h1
      have a1 := Fintype.mem_piFinset.1 ht
      constructor
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro s _ hs
        have := a1 s
        split_ifs at this with hst
        · rw [Finset.mem_singleton] at this; exact hbr (hs.symm.trans this)
        · exact ((memC _).1 this).1 hs
      · rw [Finset.card_le_one]
        intro x hx y hy
        have ex : x = t := by
          by_contra hxt
          have := a1 x; rw [if_neg hxt] at this
          exact ((memC _).1 this).2 (Finset.mem_filter.1 hx).2
        have ey : y = t := by
          by_contra hyt
          have := a1 y; rw [if_neg hyt] at this
          exact ((memC _).1 this).2 (Finset.mem_filter.1 hy).2
        rw [ex, ey]
  calc (Fintype.card J - 2) ^ N + N * (Fintype.card J - 2) ^ (N - 1)
      = S0.card + ∑ t : Fin N, (St t).card := by
        rw [hS0, Finset.sum_congr rfl (fun t _ => hSt t), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
    _ = (S0 ∪ Finset.univ.biUnion St).card := by
        rw [Finset.card_union_of_disjoint hdisj1, Finset.card_biUnion hdisj2]
    _ ≤ _ := Finset.card_le_card hsub

end C9count


section C9algsum

/-- sum over all draw sequences of ALG, tight family (natural numbers). -/
theorem tight_alg_sum {m : ℕ} {blue : Finset (V4 m × V4 m)}
    (hcol : IsTSMColoring (tightFlow m) blue) (N : ℕ) :
    ∑ ω : Fin N → V4 m, (tsmRun blue (tightFlow m \ blue) ω).card ≤
      (3 * m) * (Fintype.card (Fin N → V4 m) -
        ((Fintype.card (V4 m) - 2) ^ N + N * (Fintype.card (V4 m) - 2) ^ (N - 1))) := by
  set T : Finset (V4 m) := Finset.univ.filter (fun a => a.1 ≠ 0) with hT
  let good : V4 m → (Fin N → V4 m) → Prop := fun a ω =>
    (Finset.univ.filter (fun t => ω t = bAd blue a)).card = 0 ∧
      (Finset.univ.filter (fun t => ω t = rAd blue a)).card ≤ 1
  have hsub : ∀ ω, tsmRun blue (tightFlow m \ blue) ω ⊆ T.filter (fun a => ¬ good a ω) := by
    intro ω a ha
    rw [Finset.mem_filter, hT, Finset.mem_filter]
    refine ⟨⟨Finset.mem_univ _, ?_⟩, fun hg => tight_unassigned hcol ω a hg.1 hg.2 ha⟩
    obtain ⟨j, hj⟩ := alg_mem ha
    have hF : (a, j) ∈ tightFlow m := by
      rcases hj with ⟨hb, -⟩ | ⟨hr, -⟩
      · exact hcol.1 hb
      · exact (Finset.mem_sdiff.1 hr).1
    exact (tags_ne0 _ _ (mem_tightFlow.1 hF).2).1
  have hTc : T.card ≤ 3 * m := by
    have hcov : T ⊆ Finset.univ.filter (fun a : V4 m => a.1 = 1) ∪
        Finset.univ.filter (fun a : V4 m => a.1 = 2) ∪ Finset.univ.filter (fun a : V4 m => a.1 = 3) := by
      intro a ha
      rw [hT, Finset.mem_filter] at ha
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      have : ∀ τ : Fin 4, τ ≠ 0 → τ = 1 ∨ τ = 2 ∨ τ = 3 := by decide
      rcases this _ ha.2 with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    have := Finset.card_le_card hcov
    have e1 := Finset.card_union_le (Finset.univ.filter (fun a : V4 m => a.1 = 1) ∪
        Finset.univ.filter (fun a : V4 m => a.1 = 2)) (Finset.univ.filter (fun a : V4 m => a.1 = 3))
    have e2 := Finset.card_union_le (Finset.univ.filter (fun a : V4 m => a.1 = 1))
        (Finset.univ.filter (fun a : V4 m => a.1 = 2))
    have c1 := card_tag_fst m 1
    have c2 := card_tag_fst m 2
    have c3 := card_tag_fst m 3
    omega
  have hbad : ∀ a ∈ T, (Finset.univ.filter (fun ω : Fin N → V4 m => ¬ good a ω)).card ≤
      Fintype.card (Fin N → V4 m) -
        ((Fintype.card (V4 m) - 2) ^ N + N * (Fintype.card (V4 m) - 2) ^ (N - 1)) := by
    intro a ha
    rw [hT, Finset.mem_filter] at ha
    have hg : (Fintype.card (V4 m) - 2) ^ N + N * (Fintype.card (V4 m) - 2) ^ (N - 1) ≤
        (Finset.univ.filter (fun ω : Fin N → V4 m => good a ω)).card :=
      card_good_ge N (bAd blue a) (rAd blue a) (bAd_ne_rAd blue a ha.2)
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin N → V4 m))) (fun ω => good a ω)
    rw [Finset.card_univ] at hsplit
    omega
  calc ∑ ω : Fin N → V4 m, (tsmRun blue (tightFlow m \ blue) ω).card
      ≤ ∑ ω : Fin N → V4 m, (T.filter (fun a => ¬ good a ω)).card :=
        Finset.sum_le_sum (fun ω _ => Finset.card_le_card (hsub ω))
    _ = ∑ a ∈ T, (Finset.univ.filter (fun ω : Fin N → V4 m => ¬ good a ω)).card := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
    _ ≤ ∑ a ∈ T, (Fintype.card (Fin N → V4 m) -
        ((Fintype.card (V4 m) - 2) ^ N + N * (Fintype.card (V4 m) - 2) ^ (N - 1))) :=
        Finset.sum_le_sum hbad
    _ = T.card * _ := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ hTc

end C9algsum

section C9real

theorem exp_neg_two_le (k : ℕ) (hk : 1 ≤ k) :
    Real.exp (-2) ≤ (1 - 2 / ((k + 2 : ℕ) : ℝ)) ^ k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : (1 + 2 / (k : ℝ)) ≤ Real.exp (2 / k) := by
    have := Real.add_one_le_exp (2 / (k : ℝ)); linarith
  have h2 : (1 + 2 / (k : ℝ)) ^ k ≤ Real.exp 2 := by
    calc _ ≤ (Real.exp (2 / k)) ^ k := pow_le_pow_left₀ (by positivity) h1 k
      _ = Real.exp 2 := by
        rw [← Real.exp_nat_mul]; congr 1; field_simp
  have h3 : (1 - 2 / ((k + 2 : ℕ) : ℝ)) = (1 + 2 / (k : ℝ))⁻¹ := by
    push_cast
    field_simp
    ring
  rw [h3, inv_pow, Real.exp_neg]
  exact inv_anti₀ (by positivity) h2

/-- the good-event probability: `G / n^n ≥ e^{-2} (2 - 6/n)` for `n = k + 2 ≥ 3`. -/
theorem good_ratio (k : ℕ) (hk : 1 ≤ k) :
    Real.exp (-2) * (2 - 6 / ((k + 2 : ℕ) : ℝ)) ≤
      ((((k + 2 - 2) ^ (k + 2) + (k + 2) * (k + 2 - 2) ^ (k + 2 - 1) : ℕ)) : ℝ) /
        ((k + 2 : ℕ) : ℝ) ^ (k + 2) := by
  have hx := exp_neg_two_le k hk
  set n : ℝ := ((k + 2 : ℕ) : ℝ) with hn
  have hnpos : (0 : ℝ) < n := by rw [hn]; positivity
  have hkn : (k : ℝ) = n * (1 - 2 / n) := by
    rw [hn]; push_cast; field_simp; ring
  set x : ℝ := 1 - 2 / n with hxdef
  have hxpos : 0 ≤ x := by
    rw [hxdef, hn]; push_cast
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  have hnat : ((((k + 2 - 2) ^ (k + 2) + (k + 2) * (k + 2 - 2) ^ (k + 2 - 1) : ℕ)) : ℝ) =
      n ^ (k + 2) * (x ^ k * (x ^ 2 + x)) := by
    have e1 : k + 2 - 2 = k := by omega
    have e2 : k + 2 - 1 = k + 1 := by omega
    rw [e1, e2]
    push_cast
    have hn2 : n * x + 2 = n := by rw [← hkn, hn]; push_cast; ring
    rw [hkn, hn2]
    ring
  rw [hnat, mul_div_cancel_left₀ _ (by positivity : n ^ (k + 2) ≠ 0)]
  have hq : 2 - 6 / n ≤ x ^ 2 + x := by
    rw [hxdef]
    have h63 : 6 / n = 3 * (2 / n) := by ring
    rw [h63]
    nlinarith [sq_nonneg (2 / n)]
  have h6 : 0 ≤ 2 - 6 / n := by
    rw [hn]; push_cast
    rw [sub_nonneg, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  calc Real.exp (-2) * (2 - 6 / n) ≤ x ^ k * (2 - 6 / n) :=
        mul_le_mul_of_nonneg_right hx h6
    _ ≤ x ^ k * (x ^ 2 + x) := mul_le_mul_of_nonneg_left hq (pow_nonneg hxpos k)

end C9real

section C9opt

/-- valid partial realization matching. -/
def VM {A I : Type} {n : ℕ} (E : Finset (A × I)) (τ : Fin n → I) (M : Finset (A × Fin n)) : Prop :=
  (∀ p ∈ M, (p.1, τ p.2) ∈ E) ∧ (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p = q) ∧
    (∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q)

theorem le_realOPT {A I : Type} [Fintype A] [DecidableEq A] [DecidableEq I] {n : ℕ}
    (E : Finset (A × I)) (τ : Fin n → I) (M : Finset (A × Fin n)) (hM : VM E τ M) :
    M.card ≤ realOPT E τ := by
  classical
  unfold realOPT
  apply Finset.le_sup (f := Finset.card)
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.subset_univ M, hM.1, hM.2.1, hM.2.2⟩

theorem VM_union {A I : Type} [DecidableEq A] {n : ℕ} {E : Finset (A × I)} {τ : Fin n → I}
    {M N : Finset (A × Fin n)} (hM : VM E τ M) (hN : VM E τ N)
    (hd : ∀ p ∈ M, ∀ q ∈ N, p.1 ≠ q.1 ∧ p.2 ≠ q.2) :
    VM E τ (M ∪ N) ∧ (M ∪ N).card = M.card + N.card := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    rcases Finset.mem_union.1 hp with h | h
    · exact hM.1 p h
    · exact hN.1 p h
  · intro p hp q hq h
    rcases Finset.mem_union.1 hp with h1 | h1 <;> rcases Finset.mem_union.1 hq with h2 | h2
    · exact hM.2.1 p h1 q h2 h
    · exact absurd h (hd p h1 q h2).1
    · exact absurd h.symm (hd q h2 p h1).1
    · exact hN.2.1 p h1 q h2 h
  · intro p hp q hq h
    rcases Finset.mem_union.1 hp with h1 | h1 <;> rcases Finset.mem_union.1 hq with h2 | h2
    · exact hM.2.2 p h1 q h2 h
    · exact absurd h (hd p h1 q h2).2
    · exact absurd h.symm (hd q h2 p h1).2
    · exact hN.2.2 p h1 q h2 h
  · apply Finset.card_union_of_disjoint
    rw [Finset.disjoint_left]
    intro p h1 h2
    exact (hd p h1 p h2).1 rfl

/-- complete bipartite S,T: a matching of size `min |S| |T|`. -/
theorem exists_matching {α β : Type} [DecidableEq α] [DecidableEq β] (S : Finset α)
    (T : Finset β) :
    ∃ M : Finset (α × β), M ⊆ S ×ˢ T ∧ M.card = min S.card T.card ∧
      (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p = q) ∧ (∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q) := by
  obtain ⟨S', hS', hS'c⟩ := Finset.exists_subset_card_eq (min_le_left S.card T.card)
  obtain ⟨T', hT', hT'c⟩ := Finset.exists_subset_card_eq (min_le_right S.card T.card)
  have hc : Fintype.card S' = Fintype.card T' := by simp [hS'c, hT'c]
  let e : S' ≃ T' := Fintype.equivOfCardEq hc
  refine ⟨S'.attach.map ⟨fun a => (a.1, (e a).1), fun a b h => Subtype.ext (congrArg Prod.fst h)⟩,
    ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_map, Finset.mem_attach, true_and] at hp
    obtain ⟨a, rfl⟩ := hp
    exact Finset.mem_product.2 ⟨hS' a.2, hT' (e a).2⟩
  · simp [hS'c]
  · intro p hp q hq h
    simp only [Finset.mem_map, Finset.mem_attach, true_and] at hp hq
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    have : a = b := Subtype.ext h
    subst this; rfl
  · intro p hp q hq h
    simp only [Finset.mem_map, Finset.mem_attach, true_and] at hp hq
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    have : a = b := e.injective (Subtype.ext h)
    subst this; rfl

theorem card_tagset (m : ℕ) (t : Fin 4) :
    (Finset.univ.filter (fun a : V4 m => a.1 = t)).card = m := by
  rw [show Finset.univ.filter (fun a : V4 m => a.1 = t) = ({t} : Finset (Fin 4)) ×ˢ Finset.univ by
    ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, and_true]]
  simp

/-- number of draws with tag `b`. -/
def cnt {m n : ℕ} (ω : Fin n → V4 m) (b : Fin 4) : ℕ :=
  (Finset.univ.filter (fun t => (ω t).1 = b)).card

/-- number of distinct drawn types with tag `b`. -/
def dst {m n : ℕ} (ω : Fin n → V4 m) (b : Fin 4) : ℕ :=
  ((Finset.univ.image ω).filter (fun j => j.1 = b)).card

def foSet {m n : ℕ} (ω : Fin n → V4 m) (b : Fin 4) : Finset (Fin n) :=
  Finset.univ.filter (fun t => (ω t).1 = b ∧ ∀ s, s < t → ω s ≠ ω t)

def foM {m n : ℕ} (ω : Fin n → V4 m) (a b : Fin 4) : Finset (V4 m × Fin n) :=
  (foSet ω b).image (fun t => ((a, (ω t).2), t))

theorem foSet_injOn {m n : ℕ} (ω : Fin n → V4 m) (b : Fin 4) :
    Set.InjOn ω (foSet ω b : Set (Fin n)) := by
  intro s hs t ht h
  simp only [foSet, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hs ht
  rcases lt_trichotomy s t with h' | h' | h'
  · exact absurd h (ht.2 s h')
  · exact h'
  · exact absurd h.symm (hs.2 t h')

theorem card_foSet {m n : ℕ} (ω : Fin n → V4 m) (b : Fin 4) : (foSet ω b).card = dst ω b := by
  unfold dst
  rw [← Finset.card_image_of_injOn (foSet_injOn ω b)]
  congr 1
  ext j
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, foSet]
  constructor
  · rintro ⟨t, ⟨ht, _⟩, rfl⟩
    exact ⟨⟨t, rfl⟩, ht⟩
  · rintro ⟨⟨t0, rfl⟩, hb⟩
    have hne : (Finset.univ.filter (fun s => ω s = ω t0)).Nonempty := ⟨t0, by simp⟩
    set t := (Finset.univ.filter (fun s => ω s = ω t0)).min' hne with ht
    have htm : ω t = ω t0 := by
      have := Finset.min'_mem _ hne
      rw [← ht] at this
      simpa using this
    refine ⟨t, ⟨by rw [htm]; exact hb, fun s hs hst => ?_⟩, htm⟩
    have : t ≤ s := Finset.min'_le _ s (by simp [hst, htm])
    exact absurd hs (not_lt.2 this)

theorem card_foM {m n : ℕ} (ω : Fin n → V4 m) (a b : Fin 4) : (foM ω a b).card = dst ω b := by
  unfold foM
  rw [Finset.card_image_of_injective _ (fun s t h => congrArg Prod.snd h), card_foSet]

theorem VM_foM {m n : ℕ} (ω : Fin n → V4 m) (a b : Fin 4)
    (hE : ∀ k : Fin m, (((a, k), (b, k)) : V4 m × V4 m) ∈ tightE m) :
    VM (tightE m) ω (foM ω a b) ∧ ∀ p ∈ foM ω a b, p.1.1 = a ∧ (ω p.2).1 = b := by
  have mem : ∀ p ∈ foM ω a b, ∃ t ∈ foSet ω b, p = ((a, (ω t).2), t) := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨t, ht, rfl⟩
  have hb : ∀ t ∈ foSet ω b, (ω t).1 = b := fun t ht => (Finset.mem_filter.1 ht).2.1
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨t, ht, rfl⟩ := mem p hp
    have : ω t = (b, (ω t).2) := Prod.ext (hb t ht) rfl
    simp only
    rw [this]; exact hE _
  · intro p hp q hq h
    obtain ⟨s, hs, rfl⟩ := mem p hp
    obtain ⟨t, ht, rfl⟩ := mem q hq
    have h2 : (ω s).2 = (ω t).2 := by simpa using h
    have : ω s = ω t := Prod.ext (by rw [hb s hs, hb t ht]) h2
    rw [foSet_injOn ω b hs ht this]
  · intro p hp q hq h
    obtain ⟨s, hs, rfl⟩ := mem p hp
    obtain ⟨t, ht, rfl⟩ := mem q hq
    simp only at h
    rw [h]
  · intro p hp
    obtain ⟨t, ht, rfl⟩ := mem p hp
    exact ⟨rfl, hb t ht⟩

/-- complete-bipartite block: ads of tag `a`, draws of tag `b`. -/
theorem exists_blockM {m n : ℕ} (ω : Fin n → V4 m) (a b : Fin 4)
    (hE : ∀ x y : V4 m, x.1 = a → y.1 = b → ((x, y) : V4 m × V4 m) ∈ tightE m) :
    ∃ M : Finset (V4 m × Fin n), VM (tightE m) ω M ∧ M.card = min m (cnt ω b) ∧
      ∀ p ∈ M, p.1.1 = a ∧ (ω p.2).1 = b := by
  obtain ⟨M, hsub, hc, h1, h2⟩ := exists_matching (Finset.univ.filter (fun x : V4 m => x.1 = a))
    (Finset.univ.filter (fun t => (ω t).1 = b))
  have tg : ∀ p ∈ M, p.1.1 = a ∧ (ω p.2).1 = b := by
    intro p hp
    have := Finset.mem_product.1 (hsub hp)
    exact ⟨(Finset.mem_filter.1 this.1).2, (Finset.mem_filter.1 this.2).2⟩
  refine ⟨M, ⟨fun p hp => hE _ _ (tg p hp).1 (tg p hp).2, h1, h2⟩, ?_, tg⟩
  rw [hc, card_tagset]; rfl

theorem sep {m n : ℕ} {ω : Fin n → V4 m} {M N : Finset (V4 m × Fin n)} {a b : Fin 4}
    (hM : ∀ p ∈ M, p.1.1 ≠ a ∧ (ω p.2).1 ≠ b) (hN : ∀ p ∈ N, p.1.1 = a ∧ (ω p.2).1 = b) :
    ∀ p ∈ M, ∀ q ∈ N, p.1 ≠ q.1 ∧ p.2 ≠ q.2 := by
  intro p hp q hq
  refine ⟨fun h => (hM p hp).1 ?_, fun h => (hM p hp).2 ?_⟩
  · rw [h]; exact (hN q hq).1
  · rw [h]; exact (hN q hq).2

/-- **C9 (i)**: OPT lower bound on the tight family. -/
theorem tight_opt_ge {m n : ℕ} (ω : Fin n → V4 m) :
    min m (cnt ω 1) + min m (cnt ω 0) + dst ω 3 + dst ω 2 ≤ realOPT (tightE m) ω := by
  obtain ⟨M1, v1, c1, t1⟩ := exists_blockM ω 0 1 (fun x y hx hy => by
    unfold tightE; simp [hx, hy])
  obtain ⟨M2, v2, c2, t2⟩ := exists_blockM ω 3 0 (fun x y hx hy => by
    unfold tightE; simp [hx, hy])
  obtain ⟨v3, t3⟩ := VM_foM ω 1 3 (fun k => by
    unfold tightE; exact Finset.mem_union_left _ (mem_tightFlow.2 (by simp)))
  obtain ⟨v4, t4⟩ := VM_foM ω 2 2 (fun k => by
    unfold tightE; exact Finset.mem_union_left _ (mem_tightFlow.2 (by simp)))
  obtain ⟨u12, k12⟩ := VM_union v1 v2 (sep (fun p hp => by
    rw [(t1 p hp).1, (t1 p hp).2]; decide) t2)
  have s12 : ∀ p ∈ M1 ∪ M2, p.1.1 ≠ 1 ∧ (ω p.2).1 ≠ 3 := by
    intro p hp
    rcases Finset.mem_union.1 hp with h | h
    · rw [(t1 p h).1, (t1 p h).2]; decide
    · rw [(t2 p h).1, (t2 p h).2]; decide
  obtain ⟨u123, k123⟩ := VM_union u12 v3 (sep s12 t3)
  have s123 : ∀ p ∈ M1 ∪ M2 ∪ foM ω 1 3, p.1.1 ≠ 2 ∧ (ω p.2).1 ≠ 2 := by
    intro p hp
    rcases Finset.mem_union.1 hp with h | h
    · rcases Finset.mem_union.1 h with h | h
      · rw [(t1 p h).1, (t1 p h).2]; decide
      · rw [(t2 p h).1, (t2 p h).2]; decide
    · rw [(t3 p h).1, (t3 p h).2]; decide
  obtain ⟨u1234, k1234⟩ := VM_union u123 v4 (sep s123 t4)
  have := le_realOPT (tightE m) ω _ u1234
  rw [k1234, k123, k12, c1, c2, card_foM, card_foM] at this
  exact this

end C9opt

section C9avg

theorem BD_cnt {m n : ℕ} (b : Fin 4) : BD n (fun ω : Fin n → V4 m => (cnt ω b : ℝ)) 1 := by
  intro ω ω' i h
  have : cnt ω b ≤ cnt ω' b + 1 := by
    unfold cnt
    calc _ ≤ (insert i (Finset.univ.filter (fun t => (ω' t).1 = b))).card := by
          apply Finset.card_le_card
          intro t ht
          rw [Finset.mem_insert, Finset.mem_filter]
          by_cases hti : t = i
          · exact Or.inl hti
          · right; refine ⟨Finset.mem_univ _, ?_⟩
            rw [← h t hti]; exact (Finset.mem_filter.1 ht).2
      _ ≤ _ := Finset.card_insert_le _ _
  dsimp only
  exact_mod_cast this

theorem BD_dst {m n : ℕ} (b : Fin 4) : BD n (fun ω : Fin n → V4 m => (dst ω b : ℝ)) 1 := by
  intro ω ω' i h
  have : dst ω b ≤ dst ω' b + 1 := by
    unfold dst
    calc _ ≤ (insert (ω i) ((Finset.univ.image ω').filter (fun j => j.1 = b))).card := by
          apply Finset.card_le_card
          intro j hj
          rw [Finset.mem_filter, Finset.mem_image] at hj
          obtain ⟨⟨t, _, rfl⟩, hb⟩ := hj
          rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_image]
          by_cases hti : t = i
          · left; rw [hti]
          · right; exact ⟨⟨t, Finset.mem_univ _, (h t hti).symm⟩, hb⟩
      _ ≤ _ := Finset.card_insert_le _ _
  dsimp only
  exact_mod_cast this

theorem card_coord {Ω : Type} [Fintype Ω] [DecidableEq Ω] {n : ℕ} (S : Finset Ω) (t : Fin n) :
    (Finset.univ.filter (fun ω : Fin n → Ω => ω t ∈ S)).card =
      S.card * Fintype.card Ω ^ (n - 1) := by
  have : Finset.univ.filter (fun ω : Fin n → Ω => ω t ∈ S) =
      Fintype.piFinset (Function.update (fun _ => (Finset.univ : Finset Ω)) t S) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hω s
      by_cases hs : s = t
      · subst hs; simpa using hω
      · simp [Function.update_of_ne hs]
    · intro hω; simpa using hω t
  rw [this, Fintype.card_piFinset, ← Finset.mul_prod_erase _ _ (Finset.mem_univ t),
    Function.update_self]
  congr 1
  rw [Finset.prod_congr rfl (g := fun _ => (Finset.univ : Finset Ω).card) (fun i hi => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])]
  rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ t)]
  simp

theorem sum_cnt {m n : ℕ} (b : Fin 4) :
    ∑ ω : Fin n → V4 m, cnt ω b = n * (m * Fintype.card (V4 m) ^ (n - 1)) := by
  unfold cnt
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have key : ∀ t : Fin n, (∑ ω : Fin n → V4 m, if (ω t).1 = b then 1 else 0) =
      m * Fintype.card (V4 m) ^ (n - 1) := by
    intro t
    rw [← Finset.card_filter]
    have := card_coord (Finset.univ.filter (fun a : V4 m => a.1 = b)) t
    rw [card_tagset] at this
    rw [← this]; congr 1; ext ω; simp
  simp [key]

theorem card_V4 (m : ℕ) : Fintype.card (V4 m) = 4 * m := by simp

theorem avg_cnt {m : ℕ} (hm : 1 ≤ m) (b : Fin 4) :
    avg (Fintype.card (V4 m)) (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (cnt ω b : ℝ)) = m := by
  unfold avg
  rw [← Nat.cast_sum, sum_cnt]
  set N := Fintype.card (V4 m) with hN
  have hN1 : 1 ≤ N := by rw [hN, card_V4]; omega
  have hpow : N * N ^ (N - 1) = N ^ N := by
    rw [← pow_succ']; congr 1; omega
  have hNpos : (0 : ℝ) < (N : ℝ) ^ N := by positivity
  have : ((N * (m * N ^ (N - 1)) : ℕ) : ℝ) = m * (N : ℝ) ^ N := by
    rw [show N * (m * N ^ (N - 1)) = m * (N * N ^ (N - 1)) by ring, hpow]; push_cast; ring
  rw [this]; field_simp

theorem dst_eq {m n : ℕ} (ω : Fin n → V4 m) (b : Fin 4) :
    dst ω b = ((Finset.univ.filter (fun a : V4 m => a.1 = b)).filter
      (fun j => ∃ t, ω t = j)).card := by
  unfold dst; congr 1; ext j; simp [and_comm]

theorem card_hit {Ω : Type} [Fintype Ω] [DecidableEq Ω] {n : ℕ} (j : Ω) :
    (Finset.univ.filter (fun ω : Fin n → Ω => ∃ t, ω t = j)).card +
      (Fintype.card Ω - 1) ^ n = Fintype.card Ω ^ n := by
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n → Ω)))
    (fun ω => ∃ t, ω t = j)
  have h2 : (Finset.univ.filter (fun ω : Fin n → Ω => ¬ ∃ t, ω t = j)) =
      Fintype.piFinset (fun _ => (Finset.univ : Finset Ω).erase j) := by
    ext ω; simp
  rw [h2, Fintype.card_piFinset] at h1
  simpa [Finset.card_erase_of_mem, Finset.prod_const] using h1

theorem sum_dst {m n : ℕ} (b : Fin 4) :
    ∑ ω : Fin n → V4 m, dst ω b + m * (Fintype.card (V4 m) - 1) ^ n =
      m * Fintype.card (V4 m) ^ n := by
  simp only [dst_eq, Finset.card_filter]
  rw [Finset.sum_comm]
  have hconst : ∀ x : ℕ, m * x = ∑ j ∈ Finset.univ.filter (fun a : V4 m => a.1 = b), x := by
    intro x; rw [Finset.sum_const, card_tagset, smul_eq_mul]
  rw [hconst, hconst, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.card_filter]
  exact card_hit j

theorem avg_dst_ge {m : ℕ} (hm : 1 ≤ m) (b : Fin 4) :
    (m : ℝ) * (1 - Real.exp (-1)) ≤
      avg (Fintype.card (V4 m)) (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (dst ω b : ℝ)) := by
  unfold avg
  have hs := sum_dst (m := m) (n := Fintype.card (V4 m)) b
  set N := Fintype.card (V4 m) with hN
  have hN1 : 1 ≤ N := by rw [hN, card_V4]; omega
  have hsR : (∑ ω : Fin N → V4 m, (dst ω b : ℝ)) =
      (m : ℝ) * (N : ℝ) ^ N - m * ((N : ℝ) - 1) ^ N := by
    have := congrArg (fun x : ℕ => (x : ℝ)) hs
    simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] at this
    rw [Nat.cast_sub hN1] at this
    push_cast at this
    linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hq : (((N : ℝ) - 1) / N) ^ N ≤ Real.exp (-1) := by
    have := Real.one_sub_div_pow_le_exp_neg (n := N) (t := 1) (by exact_mod_cast hN1)
    rw [show ((N : ℝ) - 1) / N = 1 - 1 / N by field_simp]
    exact this
  rw [hsR, le_div_iff₀ (by positivity)]
  rw [div_pow] at hq
  rw [div_le_iff₀ (by positivity)] at hq
  have hm0 : (0 : ℝ) ≤ m := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hq hm0]

end C9avg

section C9fin

theorem exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  have h := Real.add_one_le_exp (1 : ℝ)
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
  norm_num; linarith

theorem unifProb_or {Ω : Type} [Fintype Ω] (n : ℕ) (P Q : (Fin n → Ω) → Prop) :
    unifProb Ω n (fun ω => P ω ∨ Q ω) ≤ unifProb Ω n P + unifProb Ω n Q := by
  classical
  unfold unifProb
  rw [← add_div]
  gcongr
  have hsub : (Finset.univ.filter (fun ω => P ω ∨ Q ω)) ⊆
      Finset.univ.filter P ∪ Finset.univ.filter Q := by
    intro ω hω
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rw [Finset.mem_filter] at hω
    rcases hω.2 with h | h
    · exact Or.inl ⟨Finset.mem_univ _, h⟩
    · exact Or.inr ⟨Finset.mem_univ _, h⟩
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h' : ((Finset.univ.filter (fun ω => P ω ∨ Q ω)).card : ℝ) ≤
      (Finset.univ.filter P).card + (Finset.univ.filter Q).card := by exact_mod_cast h
  convert h' <;> rfl

theorem unifProb_or4 {Ω : Type} [Fintype Ω] (n : ℕ) (P Q R S : (Fin n → Ω) → Prop) :
    unifProb Ω n (fun ω => P ω ∨ Q ω ∨ R ω ∨ S ω) ≤
      unifProb Ω n P + (unifProb Ω n Q + (unifProb Ω n R + unifProb Ω n S)) := by
  refine le_trans (unifProb_or n P (fun ω => Q ω ∨ R ω ∨ S ω)) (add_le_add le_rfl ?_)
  refine le_trans (unifProb_or n Q (fun ω => R ω ∨ S ω)) (add_le_add le_rfl ?_)
  exact unifProb_or n R S

theorem tight_pointwise {m n : ℕ} (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 8)
    (a1 a0 a3 a2 : ℝ) (h1 : (m : ℝ) ≤ a1) (h0 : (m : ℝ) ≤ a0)
    (h3 : (m : ℝ) * (1 - Real.exp (-1)) ≤ a3) (h2 : (m : ℝ) * (1 - Real.exp (-1)) ≤ a2)
    (blue : Finset (V4 m × V4 m)) (ω : Fin n → V4 m) :
    ((tsmRun blue (tightFlow m \ blue) ω).card : ℝ) / (realOPT (tightE m) ω : ℝ) ≤
      ((tsmRun blue (tightFlow m \ blue) ω).card : ℝ) / (m * (4 - 2 * Real.exp (-1) - 4 * δ)) +
      4 * m * (if ((cnt ω 1 : ℝ) ≤ a1 - δ * m ∨ (cnt ω 0 : ℝ) ≤ a0 - δ * m ∨
          (dst ω 3 : ℝ) ≤ a3 - δ * m ∨ (dst ω 2 : ℝ) ≤ a2 - δ * m) then 1 else 0) := by
  set X := ((tsmRun blue (tightFlow m \ blue) ω).card : ℝ) with hX
  have hX0 : 0 ≤ X := by positivity
  have hXle : X ≤ 4 * m := by
    have := Finset.card_le_univ (tsmRun blue (tightFlow m \ blue) ω)
    rw [card_V4] at this
    rw [hX]; exact_mod_cast this
  have he := exp_neg_one_le_half
  have he0 := (Real.exp_pos (-1)).le
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hδm : 0 ≤ δ * m := mul_nonneg hδ (by linarith)
  have hK : 0 < (m : ℝ) * (4 - 2 * Real.exp (-1) - 4 * δ) := by
    apply mul_pos (by linarith); linarith
  have hA : 0 ≤ X / (m * (4 - 2 * Real.exp (-1) - 4 * δ)) := div_nonneg hX0 hK.le
  split_ifs with hb
  · have : X / (realOPT (tightE m) ω : ℝ) ≤ X := by
      rcases Nat.eq_zero_or_pos (realOPT (tightE m) ω) with h | h
      · rw [h]; simp only [Nat.cast_zero, div_zero]; exact hX0
      · exact div_le_self hX0 (by exact_mod_cast h)
    linarith
  · push_neg at hb
    obtain ⟨b1, b0, b3, b2⟩ := hb
    have hopt := tight_opt_ge (m := m) ω
    have hoptR : ((min m (cnt ω 1) + min m (cnt ω 0) + dst ω 3 + dst ω 2 : ℕ) : ℝ) ≤
        (realOPT (tightE m) ω : ℝ) := by exact_mod_cast hopt
    push_cast at hoptR
    have m1 : (m : ℝ) - δ * m ≤ min (m : ℝ) (cnt ω 1 : ℝ) := le_min (by linarith) (by linarith)
    have m0 : (m : ℝ) - δ * m ≤ min (m : ℝ) (cnt ω 0 : ℝ) := le_min (by linarith) (by linarith)
    have hge : (m : ℝ) * (4 - 2 * Real.exp (-1) - 4 * δ) ≤ (realOPT (tightE m) ω : ℝ) := by
      first | linarith | nlinarith
    have := div_le_div_of_nonneg_left hX0 hK hge
    linarith

theorem tight_bad_prob {m : ℕ} (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 ≤ δ) :
    unifProb (V4 m) (Fintype.card (V4 m)) (fun ω =>
      (cnt ω 1 : ℝ) ≤ avg (Fintype.card (V4 m))
          (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (cnt ω 1 : ℝ)) - δ * m ∨
      (cnt ω 0 : ℝ) ≤ avg (Fintype.card (V4 m))
          (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (cnt ω 0 : ℝ)) - δ * m ∨
      (dst ω 3 : ℝ) ≤ avg (Fintype.card (V4 m))
          (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (dst ω 3 : ℝ)) - δ * m ∨
      (dst ω 2 : ℝ) ≤ avg (Fintype.card (V4 m))
          (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (dst ω 2 : ℝ)) - δ * m) ≤
    4 * Real.exp (-(2 * (δ * m) ^ 2 / ((Fintype.card (V4 m) : ℝ) * 1 ^ 2))) := by
  have hN : 0 < Fintype.card (V4 m) := by rw [card_V4]; omega
  haveI : Nonempty (V4 m) := ⟨((0 : Fin 4), ⟨0, by omega⟩)⟩
  have hδm : 0 ≤ δ * m := mul_nonneg hδ (Nat.cast_nonneg m)
  have e1 := mcdiarmid_lower (Fintype.card (V4 m)) hN
    (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (cnt ω 1 : ℝ)) 1 one_pos (BD_cnt 1) (δ * m) hδm
  have e0 := mcdiarmid_lower (Fintype.card (V4 m)) hN
    (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (cnt ω 0 : ℝ)) 1 one_pos (BD_cnt 0) (δ * m) hδm
  have e3 := mcdiarmid_lower (Fintype.card (V4 m)) hN
    (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (dst ω 3 : ℝ)) 1 one_pos (BD_dst 3) (δ * m) hδm
  have e2 := mcdiarmid_lower (Fintype.card (V4 m)) hN
    (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (dst ω 2 : ℝ)) 1 one_pos (BD_dst 2) (δ * m) hδm
  refine le_trans (unifProb_or4 (Fintype.card (V4 m))
    (fun ω => (cnt ω 1 : ℝ) ≤ avg (Fintype.card (V4 m))
          (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (cnt ω 1 : ℝ)) - δ * m)
    (fun ω => (cnt ω 0 : ℝ) ≤ avg (Fintype.card (V4 m))
          (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (cnt ω 0 : ℝ)) - δ * m)
    (fun ω => (dst ω 3 : ℝ) ≤ avg (Fintype.card (V4 m))
          (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (dst ω 3 : ℝ)) - δ * m)
    (fun ω => (dst ω 2 : ℝ) ≤ avg (Fintype.card (V4 m))
          (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (dst ω 2 : ℝ)) - δ * m)) ?_
  have h4 : (4 : ℝ) * Real.exp (-(2 * (δ * m) ^ 2 / ((Fintype.card (V4 m) : ℝ) * 1 ^ 2))) =
      Real.exp (-(2 * (δ * m) ^ 2 / ((Fintype.card (V4 m) : ℝ) * 1 ^ 2))) +
      (Real.exp (-(2 * (δ * m) ^ 2 / ((Fintype.card (V4 m) : ℝ) * 1 ^ 2))) +
      (Real.exp (-(2 * (δ * m) ^ 2 / ((Fintype.card (V4 m) : ℝ) * 1 ^ 2))) +
      Real.exp (-(2 * (δ * m) ^ 2 / ((Fintype.card (V4 m) : ℝ) * 1 ^ 2))))) := by ring
  rw [h4]
  exact add_le_add e1 (add_le_add e0 (add_le_add e3 e2))

theorem tight_ratio_bound {m : ℕ} (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 8)
    {blue : Finset (V4 m × V4 m)} (hcol : IsTSMColoring (tightFlow m) blue) :
    expRatio (tightE m) (tightFlow m) blue ≤
      3 * (1 - Real.exp (-2) * (2 - 6 / (Fintype.card (V4 m) : ℝ))) /
          (4 - 2 * Real.exp (-1) - 4 * δ) +
        4 * m * (4 * Real.exp (-(2 * (δ * m) ^ 2 / ((Fintype.card (V4 m) : ℝ) * 1 ^ 2)))) := by
  classical
  have hN : 4 ≤ Fintype.card (V4 m) := by rw [card_V4]; omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have he := exp_neg_one_le_half
  have he0 := Real.exp_pos (-1)
  have hK : 2 ≤ 4 - 2 * Real.exp (-1) - 4 * δ := by linarith
  have hmK : 0 < (m : ℝ) * (4 - 2 * Real.exp (-1) - 4 * δ) := mul_pos (by linarith) (by linarith)
  have hP : (0 : ℝ) < (Fintype.card (V4 m) : ℝ) ^ (Fintype.card (V4 m)) := by positivity
  have hpt := fun ω : Fin (Fintype.card (V4 m)) → V4 m => tight_pointwise hm δ hδ.le hδ1
    (avg (Fintype.card (V4 m)) (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (cnt ω 1 : ℝ)))
    (avg (Fintype.card (V4 m)) (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (cnt ω 0 : ℝ)))
    (avg (Fintype.card (V4 m)) (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (dst ω 3 : ℝ)))
    (avg (Fintype.card (V4 m)) (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (dst ω 2 : ℝ)))
    (avg_cnt hm 1).ge (avg_cnt hm 0).ge (avg_dst_ge hm 3) (avg_dst_ge hm 2) blue ω
  have hsum := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) => hpt ω)
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, Finset.sum_boole] at hsum
  have hbad := tight_bad_prob hm δ hδ.le
  unfold unifProb at hbad
  have hbad' : ((Finset.univ.filter (fun ω : Fin (Fintype.card (V4 m)) → V4 m =>
      (cnt ω 1 : ℝ) ≤ avg (Fintype.card (V4 m))
          (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (cnt ω 1 : ℝ)) - δ * m ∨
      (cnt ω 0 : ℝ) ≤ avg (Fintype.card (V4 m))
          (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (cnt ω 0 : ℝ)) - δ * m ∨
      (dst ω 3 : ℝ) ≤ avg (Fintype.card (V4 m))
          (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (dst ω 3 : ℝ)) - δ * m ∨
      (dst ω 2 : ℝ) ≤ avg (Fintype.card (V4 m))
          (fun ω : Fin (Fintype.card (V4 m)) → V4 m => (dst ω 2 : ℝ)) - δ * m)).card : ℝ) /
      (Fintype.card (V4 m) : ℝ) ^ (Fintype.card (V4 m)) ≤
      4 * Real.exp (-(2 * (δ * m) ^ 2 / ((Fintype.card (V4 m) : ℝ) * 1 ^ 2))) := by
    convert hbad
  -- ALG sum
  have hS := tight_alg_sum hcol (Fintype.card (V4 m))
  rw [Fintype.card_fun, Fintype.card_fin] at hS
  have hg := good_ratio (Fintype.card (V4 m) - 2) (by omega)
  rw [Nat.sub_add_cancel (by omega : 2 ≤ Fintype.card (V4 m))] at hg
  rw [le_div_iff₀ hP] at hg
  have he2 : Real.exp (-2) ≤ 1 / 4 := by
    have : Real.exp (-2) = Real.exp (-1) ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h := exp_neg_one_le_half
    have h0 := (Real.exp_pos (-1)).le
    first | linarith [mul_le_mul h h h0 (by norm_num : (0:ℝ) ≤ 1 / 2)] | nlinarith
  have he20 := (Real.exp_pos (-2)).le
  have hNR : (4 : ℝ) ≤ (Fintype.card (V4 m) : ℝ) := by exact_mod_cast hN
  have hc6 : 0 ≤ 6 / (Fintype.card (V4 m) : ℝ) := by positivity
  have hc1 : Real.exp (-2) * (2 - 6 / (Fintype.card (V4 m) : ℝ)) ≤ 1 := by
    first | linarith [mul_nonneg he20 hc6] | nlinarith
  have hA' : (∑ ω : Fin (Fintype.card (V4 m)) → V4 m,
      ((tsmRun blue (tightFlow m \ blue) ω).card : ℝ)) ≤
      3 * m * (1 - Real.exp (-2) * (2 - 6 / (Fintype.card (V4 m) : ℝ))) *
        (Fintype.card (V4 m) : ℝ) ^ (Fintype.card (V4 m)) := by
    rw [← Nat.cast_sum]
    rcases le_total ((Fintype.card (V4 m) - 2) ^ Fintype.card (V4 m) +
        Fintype.card (V4 m) * (Fintype.card (V4 m) - 2) ^ (Fintype.card (V4 m) - 1))
        (Fintype.card (V4 m) ^ Fintype.card (V4 m)) with hle | hle
    · have hSR := (Nat.cast_le (α := ℝ)).2 hS
      rw [Nat.cast_mul, Nat.cast_sub hle] at hSR
      have hm3 : (0 : ℝ) ≤ 3 * m := by positivity
      have hgm := mul_le_mul_of_nonneg_left hg hm3
      push_cast at hSR hgm ⊢
      linarith
    · rw [Nat.sub_eq_zero_of_le hle, mul_zero] at hS
      have : (∑ ω : Fin (Fintype.card (V4 m)) → V4 m,
          (tsmRun blue (tightFlow m \ blue) ω).card) = 0 := Nat.le_zero.1 hS
      rw [this, Nat.cast_zero]
      have : 0 ≤ 1 - Real.exp (-2) * (2 - 6 / (Fintype.card (V4 m) : ℝ)) := by linarith
      positivity
  have hB' := (div_le_iff₀ hP).1 hbad'
  have h1 : (∑ ω : Fin (Fintype.card (V4 m)) → V4 m,
      ((tsmRun blue (tightFlow m \ blue) ω).card : ℝ)) / (m * (4 - 2 * Real.exp (-1) - 4 * δ)) ≤
      3 * (1 - Real.exp (-2) * (2 - 6 / (Fintype.card (V4 m) : ℝ))) /
          (4 - 2 * Real.exp (-1) - 4 * δ) * (Fintype.card (V4 m) : ℝ) ^ (Fintype.card (V4 m)) := by
    rw [div_le_iff₀ hmK]
    refine le_trans hA' (le_of_eq ?_)
    have : (4 - 2 * Real.exp (-1) - 4 * δ) ≠ 0 := by linarith
    field_simp
  unfold expRatio
  show (∑ ω : Fin (Fintype.card (V4 m)) → V4 m, _) /
    ((Fintype.card (V4 m) : ℝ)) ^ (Fintype.card (V4 m)) ≤ _
  rw [div_le_iff₀ hP]
  have h4m : (0 : ℝ) ≤ 4 * m := by positivity
  first | linarith [mul_le_mul_of_nonneg_left hB' h4m] | nlinarith [mul_le_mul_of_nonneg_left hB' h4m]

theorem tail_small (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ M0 : ℕ, ∀ m : ℕ, M0 ≤ m → 1 ≤ m → 16 * (m : ℝ) * Real.exp (-(c * m)) ≤ η := by
  refine ⟨⌈64 / (c ^ 2 * η)⌉₊ + 1, fun m hm hm1 => ?_⟩
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hceil : 64 / (c ^ 2 * η) < m := by
    have := Nat.le_ceil (64 / (c ^ 2 * η))
    have h2 : ((⌈64 / (c ^ 2 * η)⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
    push_cast at h2; linarith
  have hm64 : 64 < m * (c ^ 2 * η) := by rwa [div_lt_iff₀ (by positivity)] at hceil
  have hy0 : 0 < c * m := by positivity
  have hexp : (c * m) ^ 2 / 4 ≤ Real.exp (c * m) := by
    have h1 := Real.add_one_le_exp (c * m / 2)
    have h2 : Real.exp (c * m) = Real.exp (c * m / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h2]
    have h3 : c * m / 2 ≤ Real.exp (c * m / 2) := by linarith
    first | linarith [mul_le_mul h3 h3 (by positivity) (by positivity)] | nlinarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  calc 16 * (m : ℝ) ≤ η * ((c * m) ^ 2 / 4) := by
        first | linarith [mul_le_mul_of_nonneg_left hm64.le (by positivity : (0:ℝ) ≤ m)] | nlinarith
    _ ≤ η * Real.exp (c * m) := by gcongr

/-- **Clause 3** of the target. -/
theorem clause3 : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      IsMaxTwoMatching (tightE m) (tightFlow m) ∧
        ∀ blue : Finset ((Fin 4 × Fin m) × (Fin 4 × Fin m)),
          IsTSMColoring (tightFlow m) blue → expRatio (tightE m) (tightFlow m) blue ≤ alpha + ε := by
  intro ε hε
  set δ : ℝ := min (1 / 8) (ε / 6) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 8 := min_le_left _ _
  have hδ2 : δ ≤ ε / 6 := min_le_right _ _
  obtain ⟨M0, hM0⟩ := tail_small (δ ^ 2 / 2) (ε / 3) (by positivity) (by positivity)
  refine ⟨max M0 (⌈6 / ε⌉₊ + 1), fun m hm => ⟨tight_isMax m, fun blue hcol => ?_⟩⟩
  have hm0 : M0 ≤ m := le_trans (le_max_left _ _) hm
  have hm1 : ⌈6 / ε⌉₊ + 1 ≤ m := le_trans (le_max_right _ _) hm
  have hm1' : 1 ≤ m := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1'
  have hme : 6 ≤ ε * m := by
    have := Nat.le_ceil (6 / ε)
    have h2 : ((⌈6 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm1
    push_cast at h2
    have h3 : 6 / ε ≤ m := by linarith
    rwa [div_le_iff₀ hε, mul_comm] at h3
  have hb := tight_ratio_bound hm1' δ hδ0 hδ1 hcol
  have hNR : ((Fintype.card (V4 m) : ℕ) : ℝ) = 4 * m := by rw [card_V4]; push_cast; ring
  rw [hNR] at hb
  have hmne : (m : ℝ) ≠ 0 := by positivity
  have hexpo : 2 * (δ * m) ^ 2 / (4 * (m : ℝ) * 1 ^ 2) = δ ^ 2 / 2 * m := by
    field_simp; ring
  rw [hexpo] at hb
  have ht := hM0 m hm0 hm1'
  set x := Real.exp (-1) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x ≤ 1 / 2 := exp_neg_one_le_half
  have hx2 : Real.exp (-2) = x ^ 2 := by rw [hx, ← Real.exp_nat_mul]; norm_num
  have halpha : alpha = 3 * (1 - 2 * x ^ 2) / (4 - 2 * x) := by
    unfold alpha
    have e1 : Real.exp 1 = x⁻¹ := by rw [hx, Real.exp_neg, inv_inv]
    have e2 : Real.exp 2 = (x ^ 2)⁻¹ := by rw [← hx2, Real.exp_neg, inv_inv]
    have hx' : (4 - 2 * x) ≠ 0 := by linarith
    rw [e1, e2]; field_simp
  rw [hx2] at hb
  rw [halpha]
  set K := 4 - 2 * x - 4 * δ with hK
  have hK25 : 5 / 2 ≤ K := by rw [hK]; linarith
  have hK0 : 3 ≤ 4 - 2 * x := by linarith
  have hKne : K ≠ 0 := by linarith
  have hK0ne : 4 - 2 * x ≠ 0 := by linarith
  have hP1 : 3 * (1 - 2 * x ^ 2) ≤ 4 - 2 * x := by linarith [sq_nonneg (x - 1 / 6)]
  have hxx : x * x ≤ 1 / 2 * (1 / 2) := mul_le_mul hx1 hx1 hx0.le (by norm_num)
  have hPpos : 0 ≤ 3 * (1 - 2 * x ^ 2) := by linarith
  have ta : 3 * (1 - 2 * x ^ 2) / K ≤ 3 * (1 - 2 * x ^ 2) / (4 - 2 * x) + ε / 3 := by
    have hdiff : 3 * (1 - 2 * x ^ 2) / K - 3 * (1 - 2 * x ^ 2) / (4 - 2 * x) =
        4 * δ * (3 * (1 - 2 * x ^ 2)) / (K * (4 - 2 * x)) := by
      field_simp
      rw [hK]; ring
    have hle : 4 * δ * (3 * (1 - 2 * x ^ 2)) / (K * (4 - 2 * x)) ≤ ε / 3 := by
      rw [div_le_iff₀ (by positivity)]
      calc 4 * δ * (3 * (1 - 2 * x ^ 2)) ≤ 4 * δ * (4 - 2 * x) :=
            mul_le_mul_of_nonneg_left hP1 (by positivity)
        _ ≤ 4 * (ε / 6) * (4 - 2 * x) := by
          have := mul_le_mul_of_nonneg_right hδ2 (show (0:ℝ) ≤ 4 - 2 * x by linarith)
          linarith
        _ ≤ ε / 3 * (K * (4 - 2 * x)) := by
          have hεK0 : 0 ≤ ε * (4 - 2 * x) := mul_nonneg hε.le (by linarith)
          linarith [mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ K by linarith) hεK0]
    linarith
  have tb : 3 * (1 - x ^ 2 * (2 - 6 / (4 * m))) / K =
      3 * (1 - 2 * x ^ 2) / K + 18 * x ^ 2 / (4 * m * K) := by
    field_simp; ring
  have tc : 18 * x ^ 2 / (4 * m * K) ≤ ε / 3 := by
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul hme hK25 (by norm_num) (by positivity)
    linarith
  have hfin : 4 * (m : ℝ) * (4 * Real.exp (-(δ ^ 2 / 2 * m))) =
      16 * (m : ℝ) * Real.exp (-(δ ^ 2 / 2 * m)) := by ring
  rw [hfin, tb] at hb
  linarith

end C9fin

end FMMMProof

namespace FMMMProof

section C6alg
variable {A J : Type} [DecidableEq A] [DecidableEq J]

theorem bc_eq_single {X : Finset (A × J)} {a : A} {j : J} (h : (a, j) ∈ X)
    (hu : ∀ a', (a', j) ∈ X → a' = a) : bc X j = {a} := by
  have him : (X.filter (fun e => e.2 = j)).image Prod.fst = {a} := by
    ext b
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨e, ⟨he, hej⟩, rfl⟩
      exact hu e.1 (by rw [← hej]; exact he)
    · rintro rfl
      exact ⟨(b, j), ⟨h, rfl⟩, rfl⟩
  unfold bc
  rw [him, if_pos (Finset.card_singleton a)]

/-- converse of `alg_mem` (blue): a hit on the unique-blue copy assigns its ad. -/
theorem mem_alg_blue {n : ℕ} {blue red : Finset (A × J)} {ω : Fin n → J} {a : A} {j : J}
    (hb : (a, j) ∈ blue) (hu : ∀ a', (a', j) ∈ blue → a' = a)
    (hc : 1 ≤ (Finset.univ.filter (fun t => ω t = j)).card) :
    a ∈ FMMM.TSM.tsmRun blue red ω := by
  rw [tsmRun_eq_ofList, mem_ofList]
  refine ⟨j, List.count_pos_iff.1 (by rw [count_map_finRange]; omega), Or.inl ?_⟩
  rw [bc_eq_single hb hu]; exact Finset.mem_singleton_self a

/-- converse of `alg_mem` (red): two hits on the unique-red copy assign its ad. -/
theorem mem_alg_red {n : ℕ} {blue red : Finset (A × J)} {ω : Fin n → J} {a : A} {j : J}
    (hr : (a, j) ∈ red) (hu : ∀ a', (a', j) ∈ red → a' = a)
    (hc : 2 ≤ (Finset.univ.filter (fun t => ω t = j)).card) :
    a ∈ FMMM.TSM.tsmRun blue red ω := by
  rw [tsmRun_eq_ofList, mem_ofList]
  refine ⟨j, List.count_pos_iff.1 (by rw [count_map_finRange]; omega),
    Or.inr ⟨by rw [count_map_finRange]; exact hc, ?_⟩⟩
  rw [bc_eq_single hr hu]; exact Finset.mem_singleton_self a

end C6alg

end FMMMProof

open FMMMProof

open FMMM.TSM
namespace TSMnum

noncomputable def x : ℝ := Real.exp (-1)

theorem x_pos : 0 < x := Real.exp_pos _

theorem x_bounds : (0.3678 : ℝ) < x ∧ x < 0.3679 := by
  have hE1 := Real.exp_one_gt_d9
  have hE2 := Real.exp_one_lt_d9
  have hm : x * Real.exp 1 = 1 := by unfold x; rw [← Real.exp_add]; simp
  have hxpos : 0 < x := x_pos
  constructor <;> nlinarith

theorem alpha_eq : alpha = 3 * (1 - 2 * x ^ 2) / (4 - 2 * x) := by
  unfold alpha x
  have hE : 0 < Real.exp 1 := Real.exp_pos 1
  rw [Real.exp_neg, show Real.exp 2 = Real.exp 1 ^ 2 by
    rw [← Real.exp_nat_mul]; norm_num]
  set E := Real.exp 1 with hEdef
  have e1 : 2 / E ^ 2 = 2 * (E⁻¹) ^ 2 := by rw [inv_pow, div_eq_mul_inv]
  have e2 : 2 / (3 * E) = 2 * E⁻¹ / 3 := by
    rw [mul_comm 3 E, ← div_div, div_eq_mul_inv 2 E]
  rw [e1, e2, show (4:ℝ) / 3 - 2 * E⁻¹ / 3 = (4 - 2 * E⁻¹) / 3 by ring, div_div_eq_mul_div]
  ring

/-- limit constants. -/
noncomputable def qL : ℝ := 1 - x
noncomputable def rL : ℝ := 2 - 3 * x
noncomputable def bL : ℝ := 1 - 2 * x ^ 2
noncomputable def bbL : ℝ := 1 - x ^ 2
noncomputable def rhoL : ℝ := 1 - 2 * x
noncomputable def tauL : ℝ := (bL - alpha) / 2

theorem alpha_mul_le (K M : ℝ) (h : 3 * (1 - 2 * x ^ 2) * K ≤ M * (4 - 2 * x)) :
    alpha * K ≤ M := by
  have hb := x_bounds
  have hd : 0 < 4 - 2 * x := by linarith
  rw [alpha_eq, div_mul_eq_mul_div, div_le_iff₀ hd]
  exact h

theorem le_alpha_mul (K M : ℝ) (h : M * (4 - 2 * x) ≤ 3 * (1 - 2 * x ^ 2) * K) :
    M ≤ alpha * K := by
  have hb := x_bounds
  have hd : 0 < 4 - 2 * x := by linarith
  rw [alpha_eq, div_mul_eq_mul_div, le_div_iff₀ hd]
  exact h

theorem alpha_pos : 0 < alpha := by
  have hb := x_bounds
  have hd : 0 < 4 - 2 * x := by linarith
  rw [alpha_eq]; apply div_pos _ hd; nlinarith

theorem n_alpha_le_b : alpha * 1 ≤ bL := by
  have hb := x_bounds; apply alpha_mul_le; unfold bL; nlinarith

theorem n_tau_nonneg : 0 ≤ tauL := by
  have := n_alpha_le_b; unfold tauL; linarith

theorem n_YZ2 : alpha * (1 / 2 + rL / 2) ≤ bL := by
  have hb := x_bounds; apply alpha_mul_le; unfold bL rL; nlinarith

theorem n_YZ1 : bL - alpha * (1 / 2 + qL) + tauL = 0 := by
  have hb := x_bounds
  have hd : 0 < 4 - 2 * x := by linarith
  unfold tauL bL qL
  rw [alpha_eq]; field_simp; ring

theorem n_BB : alpha * (1 / 2 + qL) ≤ bbL := by
  have hb := x_bounds; apply alpha_mul_le; unfold bbL qL; nlinarith

theorem n_RB : alpha * (2 * qL) ≤ qL + rhoL := by
  have hb := x_bounds; apply alpha_mul_le; unfold qL rhoL; nlinarith

theorem n_NEG2B : alpha * (1 / 2 + qL) - bL ≤ qL - alpha * qL := by
  have hb := x_bounds
  have h : alpha * (1 / 2 + 2 * qL) ≤ qL + bL := by
    apply alpha_mul_le; unfold qL bL; nlinarith
  linarith

theorem n_half_le_q : 1 / 2 ≤ qL := by have hb := x_bounds; unfold qL; linarith
theorem n_r_le_q : rL / 2 ≤ qL := by have hb := x_bounds; unfold rL qL; linarith
theorem n_alpha_le_one : alpha ≤ 1 := by
  have := n_alpha_le_b; have hb := x_bounds; unfold bL at this; nlinarith
theorem n_b_le_bb : bL ≤ bbL := by have hb := x_bounds; unfold bL bbL; nlinarith
theorem n_rho_nonneg : 0 ≤ rhoL := by have hb := x_bounds; unfold rhoL; linarith
theorem n_rho_le_q : rhoL ≤ qL := by have hb := x_bounds; unfold rhoL qL; linarith
theorem n_q_le_b : qL ≤ bL := by have hb := x_bounds; unfold qL bL; nlinarith

theorem n_NEG2BB : alpha * (1 / 2 + qL) - bL ≤ bbL - alpha * (1 / 2 + qL) := by
  have hb := x_bounds
  have h : alpha * (1 + 2 * qL) ≤ bbL + bL := by
    apply alpha_mul_le; unfold qL bL bbL; nlinarith
  linarith

end TSMnum
section C9col
variable {A J : Type} [DecidableEq A] [DecidableEq J]

theorem red_parity {F blue : Finset (A × J)} {p : List (A ⊕ J)}
    (hblue : ∀ (i : ℕ) (e : A × J), pieceEdge p i = some e →
        (e ∈ blue ↔
          ((p.Nodup ∧ Even (p.length - 1) ∧ ∃ j : J, p.head? = some (Sum.inr j)) ∧
              (i ≤ 1 ∨ Odd i)) ∨
          (¬ (p.Nodup ∧ Even (p.length - 1) ∧ ∃ j : J, p.head? = some (Sum.inr j)) ∧ Even i)))
    {k : ℕ} {e : A × J} (hk : pieceEdge p k = some e) (hb : e ∉ blue) :
    ((p.Nodup ∧ Even (p.length - 1) ∧ ∃ j : J, p.head? = some (Sum.inr j)) → 1 < k ∧ Even k) ∧
    (¬ (p.Nodup ∧ Even (p.length - 1) ∧ ∃ j : J, p.head? = some (Sum.inr j)) → Odd k) := by
  have h := hblue k e hk
  constructor
  · intro hsp
    constructor
    · by_contra hle
      push_neg at hle
      exact hb (h.2 (Or.inl ⟨hsp, Or.inl hle⟩))
    · rcases Nat.even_or_odd k with he | ho
      · exact he
      · exact absurd (h.2 (Or.inl ⟨hsp, Or.inr ho⟩)) hb
  · intro hsp
    rcases Nat.even_or_odd k with he | ho
    · exact absurd (h.2 (Or.inr ⟨hsp, he⟩)) hb
    · exact ho

/-- (F1) no ad carries two red edges. -/
theorem not_both_red {F blue : Finset (A × J)} (hcol : IsTSMColoring F blue)
    {a : A} {j1 j2 : J} (hne : j1 ≠ j2) (h1 : (a, j1) ∈ F) (h1' : (a, j1) ∉ blue)
    (h2 : (a, j2) ∈ F) (h2' : (a, j2) ∉ blue) : False := by
  obtain ⟨-, pieces, hdisj, hcov, hpc⟩ := hcol
  obtain ⟨p, hp, i, hi⟩ := hcov _ h1
  obtain ⟨q, hq, i', hi'⟩ := hcov _ h2
  have memA : ∀ (r : List (A ⊕ J)) (k : ℕ) (jj : J), pieceEdge r k = some (a, jj) →
      Sum.inl a ∈ r := by
    intro r k jj h
    rcases pieceEdge_some h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact List.mem_iff_getElem?.2 ⟨_, h1⟩
    · exact List.mem_iff_getElem?.2 ⟨_, h2⟩
  have hpq : p = q := by
    by_contra hpq
    haveI : Std.Symm (fun p q : List (A ⊕ J) => ∀ v ∈ p, v ∉ q) :=
      ⟨fun x y h v hv hvx => h v hvx hv⟩
    exact List.Pairwise.forall hdisj hp hq hpq _ (memA p i j1 hi) (memA q i' j2 hi')
  subst hpq
  obtain ⟨-, hshape, hblue⟩ := hpc p hp
  have hii : i ≠ i' := by
    rintro rfl
    rw [hi] at hi'
    exact hne (congrArg Prod.snd (Option.some.inj hi'))
  have posA : ∀ (k : ℕ) (jj : J), pieceEdge p k = some (a, jj) →
      ∃ s, (s = k ∨ s = k + 1) ∧ ∃ hs : s < p.length, p[s] = Sum.inl a := by
    intro k jj h
    rcases pieceEdge_some h with ⟨h1, _⟩ | ⟨_, h2⟩
    · obtain ⟨hs, e⟩ := getE h1
      exact ⟨k, Or.inl rfl, hs, e⟩
    · obtain ⟨hs, e⟩ := getE h2
      exact ⟨k + 1, Or.inr rfl, hs, e⟩
  obtain ⟨s, hs, hsl, es⟩ := posA i j1 hi
  obtain ⟨s', hs', hsl', es'⟩ := posA i' j2 hi'
  have r1 := red_parity (F := F) hblue hi h1'
  have r2 := red_parity (F := F) hblue hi' h2'
  have cons : s = s' → False := by
    intro hss
    by_cases hsp : (p.Nodup ∧ Even (p.length - 1) ∧ ∃ j : J, p.head? = some (Sum.inr j))
    · obtain ⟨-, ⟨x1, hx1⟩⟩ := r1.1 hsp
      obtain ⟨-, ⟨x2, hx2⟩⟩ := r2.1 hsp
      omega
    · obtain ⟨x1, hx1⟩ := r1.2 hsp
      obtain ⟨x2, hx2⟩ := r2.2 hsp
      omega
  rcases hshape with ⟨hnd, -, -, -⟩ | ⟨hlen, hhl, hdl⟩
  · exact cons ((List.Nodup.getElem_inj_iff hnd).1 (es.trans es'.symm))
  · have hnn : ¬ p.Nodup := by
      intro hnd
      have h1 : p[0]? = p[p.length - 1]? := by
        rw [← List.head?_eq_getElem?, ← List.getLast?_eq_getElem?]; exact hhl
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
      have := (List.Nodup.getElem_inj_iff hnd).1 (Option.some.inj h1)
      omega
    have hsp : ¬ (p.Nodup ∧ Even (p.length - 1) ∧ ∃ j : J, p.head? = some (Sum.inr j)) :=
      fun h => hnn h.1
    obtain ⟨x1, hx1⟩ := r1.2 hsp
    obtain ⟨x2, hx2⟩ := r2.2 hsp
    rcases pos_cases p hlen hhl hdl s s' hsl hsl' (es.trans es'.symm) with h | h | h
    · exact cons h
    · omega
    · omega

end C9col
section Cprob

/-- number of draw sequences avoiding a set `S` of copies. -/
theorem card_avoid {Ω : Type} [Fintype Ω] [DecidableEq Ω] (n : ℕ) (S : Finset Ω) :
    (Finset.univ.filter (fun ω : Fin n → Ω => ∀ t, ω t ∉ S)).card =
      (Fintype.card Ω - S.card) ^ n := by
  have h : Finset.univ.filter (fun ω : Fin n → Ω => ∀ t, ω t ∉ S) =
      Fintype.piFinset (fun _ : Fin n => Sᶜ) := by
    ext ω; simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset, Finset.card_compl]
  simp

/-- eventually `(1 - x/n)^n ≤ exp(-x) + η`. -/
theorem pow_le_exp_add (x η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (1 - x / n) ^ n ≤ Real.exp (-x) + η := by
  have h := Real.tendsto_one_add_div_pow_exp (-x)
  have h2 := (tendsto_order.1 h).2 _ (lt_add_of_pos_right (Real.exp (-x)) hη)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h2
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  rw [neg_div, ← sub_eq_add_neg] at this
  exact this.le

/-- eventually `(1 - x/n)^n ≥ exp(-x) - η`. -/
theorem exp_sub_le_pow (x η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Real.exp (-x) - η ≤ (1 - x / n) ^ n := by
  have h := Real.tendsto_one_add_div_pow_exp (-x)
  have h2 := (tendsto_order.1 h).1 _ (sub_lt_self (Real.exp (-x)) hη)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h2
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  rw [neg_div, ← sub_eq_add_neg] at this
  exact this.le


theorem card_cnt_one {Ω : Type} [Fintype Ω] [DecidableEq Ω] (n : ℕ) (S : Finset Ω) (j : Ω)
    (hj : j ∉ S) :
    (Finset.univ.filter (fun ω : Fin n → Ω => (∀ t, ω t ∉ S) ∧
      (Finset.univ.filter (fun t => ω t = j)).card = 1)).card =
      n * (Fintype.card Ω - S.card - 1) ^ (n - 1) := by
  set C : Finset Ω := (insert j S)ᶜ with hC
  have hCc : C.card = Fintype.card Ω - S.card - 1 := by
    rw [hC, Finset.card_compl, Finset.card_insert_of_notMem hj]; omega
  have memC : ∀ x, x ∈ C ↔ x ≠ j ∧ x ∉ S := by
    intro x; simp [hC, not_or]
  have h : Finset.univ.filter (fun ω : Fin n → Ω => (∀ t, ω t ∉ S) ∧
      (Finset.univ.filter (fun t => ω t = j)).card = 1) =
      Finset.univ.biUnion (fun t : Fin n =>
        Fintype.piFinset (fun s => if s = t then ({j} : Finset Ω) else C)) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Fintype.mem_piFinset, Finset.card_eq_one]
    constructor
    · rintro ⟨hS, t, ht⟩
      refine ⟨t, fun s => ?_⟩
      have hs := Finset.ext_iff.1 ht s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hs
      by_cases hst : s = t
      · rw [if_pos hst, Finset.mem_singleton]; exact hs.2 hst
      · rw [if_neg hst, memC]; exact ⟨fun h => hst (hs.1 h), hS s⟩
    · rintro ⟨t, ht⟩
      refine ⟨fun s hs => ?_, t, ?_⟩
      · have := ht s
        by_cases hst : s = t
        · rw [if_pos hst, Finset.mem_singleton] at this; exact hj (this ▸ hs)
        · rw [if_neg hst, memC] at this; exact this.2 hs
      · ext s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hs
          by_contra hst
          have := ht s
          rw [if_neg hst, memC] at this
          exact this.1 hs
        · rintro rfl
          have := ht s
          rw [if_pos rfl, Finset.mem_singleton] at this
          exact this
  rw [h, Finset.card_biUnion]
  · have hp : ∀ t : Fin n, (Fintype.piFinset
        (fun s => if s = t then ({j} : Finset Ω) else C)).card = C.card ^ (n - 1) := by
      intro t
      rw [Fintype.card_piFinset, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t)]
      rw [if_pos rfl, Finset.card_singleton, one_mul]
      rw [Finset.prod_congr rfl (fun s hs => by
        rw [if_neg (Finset.ne_of_mem_erase hs)] : ∀ s ∈ Finset.univ.erase t,
          (if s = t then ({j} : Finset Ω) else C).card = C.card)]
      rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ,
        Fintype.card_fin]
    simp only [hp, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hCc]
  · intro t _ t' _ htt'
    refine Finset.disjoint_left.2 (fun ω h1 h2 => ?_)
    rw [Fintype.mem_piFinset] at h1 h2
    have a1 := h1 t
    have a2 := h2 t
    rw [if_pos rfl, Finset.mem_singleton] at a1
    rw [if_neg htt', memC] at a2
    exact a2.1 a1

theorem card_cnt_le_one {Ω : Type} [Fintype Ω] [DecidableEq Ω] (n : ℕ) (S : Finset Ω) (j : Ω)
    (hj : j ∉ S) :
    (Finset.univ.filter (fun ω : Fin n → Ω => (∀ t, ω t ∉ S) ∧
      (Finset.univ.filter (fun t => ω t = j)).card ≤ 1)).card =
      (Fintype.card Ω - S.card - 1) ^ n + n * (Fintype.card Ω - S.card - 1) ^ (n - 1) := by
  have h0 := card_avoid n (insert j S)
  rw [Finset.card_insert_of_notMem hj] at h0
  rw [← card_cnt_one n S j hj, show Fintype.card Ω - S.card - 1 = Fintype.card Ω - (S.card + 1)
    by omega, ← h0, ← Finset.card_union_of_disjoint]
  · congr 1
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_insert, not_or]
    constructor
    · rintro ⟨hS, hc⟩
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hc with h | h
      · left
        intro t
        refine ⟨fun ht => ?_, hS t⟩
        have : t ∈ Finset.univ.filter (fun t => ω t = j) := by simp [ht]
        rw [Finset.card_eq_zero.1 h] at this
        simp at this
      · right; exact ⟨hS, h⟩
    · rintro (h | ⟨hS, h⟩)
      · refine ⟨fun t => (h t).2, ?_⟩
        have : Finset.univ.filter (fun t => ω t = j) = ∅ := by
          ext t; simp [(h t).1]
        rw [this]; simp
      · exact ⟨hS, h.le⟩
  · refine Finset.disjoint_left.2 (fun ω h1 h2 => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, not_or] at h1 h2
    obtain ⟨t, ht⟩ := Finset.card_eq_one.1 h2.2
    have : t ∈ Finset.univ.filter (fun t => ω t = j) := by rw [ht]; simp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact (h1 t).1 this

/-- `(N-k)^m ≤ N^m exp(-k m/N)`. -/
theorem sub_pow_le_exp (N k m : ℕ) (hk : k ≤ N) :
    ((N - k : ℕ) : ℝ) ^ m ≤ (N : ℝ) ^ m * Real.exp (-((k : ℝ) * m / N)) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : k = 0 := by omega
    subst this; simp
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have h1 : ((N - k : ℕ) : ℝ) = N * (1 - k / N) := by
    rw [Nat.cast_sub hk]; field_simp
  have h2 : (1 - (k:ℝ) / N) ≤ Real.exp (-(k / N)) := by
    have := Real.add_one_le_exp (-((k:ℝ) / N)); linarith
  have h3 : 0 ≤ 1 - (k:ℝ) / N := by
    rw [sub_nonneg, div_le_one hNr]; exact_mod_cast hk
  rw [h1, mul_pow]
  have h4 : (1 - (k:ℝ) / N) ^ m ≤ Real.exp (-((k:ℝ) * m / N)) := by
    calc (1 - (k:ℝ) / N) ^ m ≤ (Real.exp (-(k / N))) ^ m := by gcongr
      _ = Real.exp (-((k:ℝ) * m / N)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  exact mul_le_mul_of_nonneg_left h4 (by positivity)

/-- `(m+1)^m ≤ m^m e`. -/
theorem succ_pow_le (m : ℕ) : ((m + 1 : ℕ) : ℝ) ^ m ≤ (m : ℝ) ^ m * Real.exp 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using Real.one_le_exp (zero_le_one' ℝ)
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have h1 : ((m + 1 : ℕ) : ℝ) ≤ m * Real.exp (1 / m) := by
    have := Real.add_one_le_exp (1 / m : ℝ)
    push_cast
    calc (m:ℝ) + 1 = m * (1 / m + 1) := by
          rw [mul_add, mul_one, mul_one_div_cancel hmr.ne']; ring
      _ ≤ m * Real.exp (1 / m) := by gcongr
  calc ((m + 1 : ℕ) : ℝ) ^ m ≤ (m * Real.exp (1 / m)) ^ m := by gcongr
    _ = (m:ℝ) ^ m * Real.exp 1 := by
      rw [mul_pow, ← Real.exp_nat_mul]; congr 2; field_simp


theorem avoid_le_exp {Ω : Type} [Fintype Ω] [DecidableEq Ω] (n : ℕ) (hN : Fintype.card Ω = n)
    (S : Finset Ω) :
    ((Finset.univ.filter (fun ω : Fin n → Ω => ∀ t, ω t ∉ S)).card : ℝ) ≤
      (n : ℝ) ^ n * Real.exp (-(S.card : ℝ)) := by
  rw [card_avoid, hN, Nat.cast_pow]
  have hk : S.card ≤ n := hN ▸ Finset.card_le_univ S
  have h := sub_pow_le_exp n S.card n hk
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    have : S.card = 0 := by omega
    simp [this]
  · have hnr : (n:ℝ) ≠ 0 := by positivity
    rwa [mul_div_assoc, div_self hnr, mul_one] at h

theorem avoid_cnt_le_exp {Ω : Type} [Fintype Ω] [DecidableEq Ω] (n : ℕ)
    (hN : Fintype.card Ω = n) (S : Finset Ω) (j : Ω) (hj : j ∉ S) :
    ((Finset.univ.filter (fun ω : Fin n → Ω => (∀ t, ω t ∉ S) ∧
      (Finset.univ.filter (fun t => ω t = j)).card ≤ 1)).card : ℝ) ≤
      (n : ℝ) ^ n * (Real.exp (-((S.card : ℝ) + 1)) *
        (1 + Real.exp (((S.card : ℝ) + 1) / n))) := by
  rw [card_cnt_le_one n S j hj, hN]
  have hk : S.card + 1 ≤ n := by
    have := Finset.card_le_univ (insert j S)
    rw [Finset.card_insert_of_notMem hj, hN] at this; exact this
  have hn : 0 < n := by omega
  have e1 : n - S.card - 1 = n - (S.card + 1) := by omega
  rw [e1]
  have h1 := sub_pow_le_exp n (S.card + 1) n hk
  have h2 := sub_pow_le_exp n (S.card + 1) (n - 1) hk
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hkc : ((S.card + 1 : ℕ) : ℝ) = (S.card : ℝ) + 1 := by push_cast; ring
  rw [hkc] at h1 h2
  set k : ℝ := (S.card : ℝ) + 1 with hkdef
  set X : ℝ := ((n - (S.card + 1) : ℕ) : ℝ) with hX
  have a1 : Real.exp (-(k * n / n)) = Real.exp (-k) := by
    rw [mul_div_assoc, div_self hnr.ne', mul_one]
  have a2 : Real.exp (-(k * ((n - 1 : ℕ) : ℝ) / n)) = Real.exp (-k) * Real.exp (k / n) := by
    rw [← Real.exp_add]; congr 1; rw [Nat.cast_sub (by omega : 1 ≤ n)]; field_simp; ring
  have a3 : (n:ℝ) * (n:ℝ) ^ (n - 1) = (n:ℝ) ^ n := by
    rw [← pow_succ']; congr 1; omega
  rw [a1] at h1
  rw [a2] at h2
  push_cast
  calc X ^ n + (n:ℝ) * X ^ (n - 1)
      ≤ (n:ℝ) ^ n * Real.exp (-k) + (n:ℝ) * ((n:ℝ) ^ (n - 1) * (Real.exp (-k) * Real.exp (k / n))) := by
        gcongr
    _ = (n:ℝ) ^ n * (Real.exp (-k) * (1 + Real.exp (k / n))) := by
        rw [← mul_assoc, a3]; ring

theorem card_cnt_zero {Ω : Type} [Fintype Ω] [DecidableEq Ω] (n : ℕ) (j : Ω) :
    (Finset.univ.filter (fun ω : Fin n → Ω =>
      (Finset.univ.filter (fun t => ω t = j)).card = 0)).card = (Fintype.card Ω - 1) ^ n := by
  have h := card_avoid n ({j} : Finset Ω)
  rw [Finset.card_singleton] at h
  rw [← h]
  congr 1
  ext ω
  simp [Finset.card_eq_zero, Finset.filter_eq_empty_iff]

theorem card_cnt_eq_one {Ω : Type} [Fintype Ω] [DecidableEq Ω] (n : ℕ) (j : Ω) :
    (Finset.univ.filter (fun ω : Fin n → Ω =>
      (Finset.univ.filter (fun t => ω t = j)).card = 1)).card =
      n * (Fintype.card Ω - 1) ^ (n - 1) := by
  have h := card_cnt_one n (∅ : Finset Ω) j (Finset.notMem_empty j)
  rw [Finset.card_empty, Nat.sub_zero] at h
  rw [← h]
  congr 1
  ext ω
  simp

/-- `(n-1)^(n-1) e ≥ n^(n-1)`. -/
theorem pred_pow_ge (n : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ (n - 1) * Real.exp (-1) ≤ ((n - 1 : ℕ) : ℝ) ^ (n - 1) := by
  have h := succ_pow_le (n - 1)
  rw [show n - 1 + 1 = n by omega] at h
  have he : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
  have hp : 0 < Real.exp (-1) := Real.exp_pos _
  calc (n : ℝ) ^ (n - 1) * Real.exp (-1) ≤ ((n - 1 : ℕ) : ℝ) ^ (n - 1) * Real.exp 1 * Real.exp (-1) := by
        gcongr
    _ = ((n - 1 : ℕ) : ℝ) ^ (n - 1) := by rw [mul_assoc, mul_comm (Real.exp 1), he, mul_one]

theorem min_two_eq (c : ℕ) : ((min c 2 : ℕ) : ℝ) =
    2 - 2 * (if c = 0 then (1:ℝ) else 0) - (if c = 1 then (1:ℝ) else 0) := by
  by_cases h0 : c = 0
  · subst h0; norm_num
  by_cases h1 : c = 1
  · subst h1; norm_num
  have : min c 2 = 2 := by omega
  rw [this, if_neg h0, if_neg h1]; norm_num

theorem min_one_eq (c : ℕ) : ((min c 1 : ℕ) : ℝ) = 1 - (if c = 0 then (1:ℝ) else 0) := by
  by_cases h0 : c = 0
  · subst h0; norm_num
  have : min c 1 = 1 := by omega
  rw [this, if_neg h0]; norm_num

theorem sum_min_one_le {Ω : Type} [Fintype Ω] [DecidableEq Ω] (n : ℕ) (hN : Fintype.card Ω = n)
    (hn : 0 < n) (j : Ω) :
    ∑ ω : Fin n → Ω, ((min (Finset.univ.filter (fun t => ω t = j)).card 1 : ℕ) : ℝ) ≤
      (n : ℝ) ^ n * (1 - Real.exp (-1) + Real.exp (-1) / n) := by
  simp only [min_one_eq]
  rw [Finset.sum_sub_distrib, Finset.sum_boole]
  rw [card_cnt_zero, hN]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_fin, hN,
    Finset.prod_const, nsmul_eq_mul, mul_one]
  have hp := pred_pow_ge n hn
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have a3 : (n:ℝ) * (n:ℝ) ^ (n - 1) = (n:ℝ) ^ n := by
    rw [← pow_succ']; congr 1; omega
  have b3 : ((n - 1 : ℕ) : ℝ) ^ n = ((n - 1 : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hc : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega)]; simp
  push_cast
  rw [b3]
  have key : (n:ℝ) ^ n * (1 - 1 / n) * Real.exp (-1) ≤ ((n - 1 : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) ^ (n - 1) := by
    have : (n:ℝ) ^ n * (1 - 1 / n) = ((n - 1 : ℕ) : ℝ) * (n:ℝ) ^ (n - 1) := by
      rw [hc, ← a3]; field_simp
    rw [this, mul_assoc]
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  have : (n:ℝ) ^ n * (1 - Real.exp (-1) + Real.exp (-1) / n) =
      (n:ℝ) ^ n - (n:ℝ) ^ n * (1 - 1 / n) * Real.exp (-1) := by ring
  rw [this]; linarith

theorem sum_min_two_le {Ω : Type} [Fintype Ω] [DecidableEq Ω] (n : ℕ) (hN : Fintype.card Ω = n)
    (hn : 0 < n) (j : Ω) :
    ∑ ω : Fin n → Ω, ((min (Finset.univ.filter (fun t => ω t = j)).card 2 : ℕ) : ℝ) ≤
      (n : ℝ) ^ n * (2 - 3 * Real.exp (-1) + 2 * Real.exp (-1) / n) := by
  simp only [min_two_eq]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
    Finset.sum_boole, card_cnt_zero, card_cnt_eq_one, hN]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_fin, hN,
    Finset.prod_const, nsmul_eq_mul, mul_one]
  have hp := pred_pow_ge n hn
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have a3 : (n:ℝ) * (n:ℝ) ^ (n - 1) = (n:ℝ) ^ n := by
    rw [← pow_succ']; congr 1; omega
  have b3 : ((n - 1 : ℕ) : ℝ) ^ n = ((n - 1 : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hc : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega)]; simp
  push_cast
  rw [b3]
  have key : (n:ℝ) ^ n * (1 - 1 / n) * Real.exp (-1) ≤ ((n - 1 : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) ^ (n - 1) := by
    have : (n:ℝ) ^ n * (1 - 1 / n) = ((n - 1 : ℕ) : ℝ) * (n:ℝ) ^ (n - 1) := by
      rw [hc, ← a3]; field_simp
    rw [this, mul_assoc]
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  have key2 : (n:ℝ) ^ n * Real.exp (-1) ≤ (n:ℝ) * ((n - 1 : ℕ) : ℝ) ^ (n - 1) := by
    rw [← a3, mul_assoc]
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  have : (n:ℝ) ^ n * (2 - 3 * Real.exp (-1) + 2 * Real.exp (-1) / n) =
      2 * (n:ℝ) ^ n - 2 * ((n:ℝ) ^ n * (1 - 1 / n) * Real.exp (-1)) - (n:ℝ) ^ n * Real.exp (-1) := by
    ring
  rw [this]; linarith

theorem sum_cnt_eq {Ω : Type} [Fintype Ω] [DecidableEq Ω] (n : ℕ) (hN : Fintype.card Ω = n)
    (hn : 0 < n) (j : Ω) :
    ∑ ω : Fin n → Ω, ((Finset.univ.filter (fun t => ω t = j)).card : ℝ) = (n : ℝ) ^ n := by
  have h : ∑ ω : Fin n → Ω, (Finset.univ.filter (fun t => ω t = j)).card = n ^ n := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    have key : ∀ t : Fin n, (∑ ω : Fin n → Ω, if ω t = j then 1 else 0) = n ^ (n - 1) := by
      intro t
      rw [Finset.sum_boole]
      have := card_coord ({j} : Finset Ω) t
      simp only [Finset.mem_singleton, Finset.card_singleton, one_mul, hN] at this
      exact_mod_cast this
    rw [Finset.sum_congr rfl (fun t _ => key t), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, ← pow_succ']
    congr 1; omega
  exact_mod_cast h

/-- `E[min(cnt, k)]` limit, `k ≤ 2`. -/
noncomputable def muE (k : ℕ) : ℝ :=
  if k = 0 then 0 else if k = 1 then 1 - Real.exp (-1) else 2 - 3 * Real.exp (-1)

/-- expectation of the copy-cover bound (C5 + finite-n errors): total error ≤ `n^n`. -/
theorem sum_cover_le {Ω : Type} [Fintype Ω] [DecidableEq Ω] (n : ℕ) (hN : Fintype.card Ω = n)
    (hn : 0 < n) (Yc : Ω → Prop) [DecidablePred Yc] (k : Ω → ℕ) (hk : ∀ j, k j ≤ 2) :
    ∑ ω : Fin n → Ω, ∑ j, (if Yc j then ((Finset.univ.filter (fun t => ω t = j)).card : ℝ)
      else ((min (Finset.univ.filter (fun t => ω t = j)).card (k j) : ℕ) : ℝ)) ≤
      (n : ℝ) ^ n * (∑ j, (if Yc j then (1:ℝ) else muE (k j)) + 1) := by
  have hx := Real.exp_neg_one_lt_half
  have hx0 := Real.exp_pos (-1)
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hnn : (0:ℝ) < (n:ℝ) ^ n := pow_pos hnr n
  have hinv : 0 < Real.exp (-1) / n := div_pos hx0 hnr
  have hper : ∀ j, ∑ ω : Fin n → Ω, (if Yc j then
      ((Finset.univ.filter (fun t => ω t = j)).card : ℝ)
      else ((min (Finset.univ.filter (fun t => ω t = j)).card (k j) : ℕ) : ℝ)) ≤
      (n : ℝ) ^ n * ((if Yc j then (1:ℝ) else muE (k j)) + 1 / n) := by
    intro j
    have h1n : 0 < (1:ℝ) / n := by positivity
    by_cases hy : Yc j
    · simp only [if_pos hy]
      rw [sum_cnt_eq n hN hn j]; nlinarith
    simp only [if_neg hy]
    unfold muE
    have hxn : Real.exp (-1) / n ≤ 1 / (2 * n) := by
      rw [div_le_div_iff₀ hnr (by positivity)]; nlinarith
    have h2n : 1 / (2 * (n:ℝ)) = (1 / n) / 2 := by field_simp
    have hkj := hk j
    rcases (by omega : k j = 0 ∨ k j = 1 ∨ k j = 2) with h | h | h
    · rw [h, if_pos rfl]; simp only [min_zero, Nat.cast_zero, Finset.sum_const_zero]; positivity
    · rw [h, if_neg one_ne_zero, if_pos rfl]
      have := sum_min_one_le n hN hn j
      refine this.trans ?_
      apply mul_le_mul_of_nonneg_left _ hnn.le
      linarith
    · rw [h, if_neg two_ne_zero, if_neg (by norm_num)]
      have := sum_min_two_le n hN hn j
      refine this.trans ?_
      apply mul_le_mul_of_nonneg_left _ hnn.le
      have : 2 * Real.exp (-1) / n = 2 * (Real.exp (-1) / n) := by ring
      linarith
  rw [Finset.sum_comm]
  refine (Finset.sum_le_sum (fun j _ => hper j)).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hN,
    nsmul_eq_mul]
  apply le_of_eq
  congr 1
  field_simp

end Cprob

section F2
variable {A J : Type} [DecidableEq A] [DecidableEq J]

def adDeg (F : Finset (A × J)) (a : A) : ℕ := (F.filter (fun e => e.1 = a)).card
def cpDeg (F : Finset (A × J)) (j : J) : ℕ := (F.filter (fun e => e.2 = j)).card
def IsBAd (F blue : Finset (A × J)) (b : A) : Prop := adDeg F b = 1 ∧ ∃ j, (b, j) ∈ blue
def IsBBAd (blue : Finset (A × J)) (b : A) : Prop :=
  ∃ j1 j2 : J, j1 ≠ j2 ∧ (b, j1) ∈ blue ∧ (b, j2) ∈ blue
def IsNeg1 (F blue : Finset (A × J)) (a : A) : Prop :=
  adDeg F a = 1 ∧ ∃ j, (a, j) ∈ F ∧ (a, j) ∉ blue
def IsNeg2 (F blue : Finset (A × J)) (a : A) : Prop :=
  ∃ j1 j2 : J, (a, j1) ∈ blue ∧ (a, j2) ∈ F ∧ (a, j2) ∉ blue ∧ (cpDeg F j1 = 1 ∨ cpDeg F j2 = 1)
def SPp (p : List (A ⊕ J)) : Prop :=
  p.Nodup ∧ Even (p.length - 1) ∧ ∃ j : J, p.head? = some (Sum.inr j)

theorem f2_two_le_ad {F : Finset (A × J)} {a : A} {j1 j2 : J} (hne : j1 ≠ j2)
    (h1 : (a, j1) ∈ F) (h2 : (a, j2) ∈ F) : 2 ≤ adDeg F a := by
  unfold adDeg
  have hsub : ({(a, j1), (a, j2)} : Finset (A × J)) ⊆ F.filter (fun e => e.1 = a) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [h1, h2]
  have hc : ({(a, j1), (a, j2)} : Finset (A × J)).card = 2 :=
    Finset.card_pair (by simp [hne])
  rw [← hc]; exact Finset.card_le_card hsub

theorem f2_two_le_cp {F : Finset (A × J)} {j : J} {a1 a2 : A} (hne : a1 ≠ a2)
    (h1 : (a1, j) ∈ F) (h2 : (a2, j) ∈ F) : 2 ≤ cpDeg F j := by
  unfold cpDeg
  have hsub : ({(a1, j), (a2, j)} : Finset (A × J)) ⊆ F.filter (fun e => e.2 = j) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [h1, h2]
  have hc : ({(a1, j), (a2, j)} : Finset (A × J)).card = 2 :=
    Finset.card_pair (by simp [hne])
  rw [← hc]; exact Finset.card_le_card hsub

theorem f2_nd_pos {α : Type} {p : List α} (hnd : p.Nodup) {x y : ℕ} {v : α}
    (hx : p[x]? = some v) (hy : p[y]? = some v) : x = y := by
  obtain ⟨hx1, ex⟩ := getE hx
  obtain ⟨hy1, ey⟩ := getE hy
  exact (List.Nodup.getElem_inj_iff hnd).1 (ex.trans ey.symm)

theorem f2_edge_r {F : Finset (A × J)} {p : List (A ⊕ J)}
    (hadj : ∀ i : ℕ, i + 1 < p.length → ∃ e ∈ F, pieceEdge p i = some e)
    {s : ℕ} {a : A} (hs : p[s]? = some (Sum.inl a)) (h : s + 1 < p.length) :
    ∃ j, p[s+1]? = some (Sum.inr j) ∧ (a, j) ∈ F ∧ pieceEdge p s = some (a, j) := by
  obtain ⟨⟨a', j⟩, hF, he⟩ := hadj s h
  rcases pieceEdge_some he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hs] at h1
    simp only [Option.some.injEq, Sum.inl.injEq] at h1
    subst h1
    exact ⟨j, h2, hF, he⟩
  · rw [hs] at h1; simp at h1

theorem f2_edge_l {F : Finset (A × J)} {p : List (A ⊕ J)}
    (hadj : ∀ i : ℕ, i + 1 < p.length → ∃ e ∈ F, pieceEdge p i = some e)
    {s : ℕ} {a : A} (hs : p[s+1]? = some (Sum.inl a)) :
    ∃ j, p[s]? = some (Sum.inr j) ∧ (a, j) ∈ F ∧ pieceEdge p s = some (a, j) := by
  obtain ⟨⟨a', j⟩, hF, he⟩ := hadj s (getE hs).1
  rcases pieceEdge_some he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hs] at h2; simp at h2
  · rw [hs] at h2
    simp only [Option.some.injEq, Sum.inl.injEq] at h2
    subst h2
    exact ⟨j, h1, hF, he⟩

theorem f2_edge_r' {F : Finset (A × J)} {p : List (A ⊕ J)}
    (hadj : ∀ i : ℕ, i + 1 < p.length → ∃ e ∈ F, pieceEdge p i = some e)
    {s : ℕ} {j : J} (hs : p[s]? = some (Sum.inr j)) (h : s + 1 < p.length) :
    ∃ a, p[s+1]? = some (Sum.inl a) ∧ (a, j) ∈ F ∧ pieceEdge p s = some (a, j) := by
  obtain ⟨⟨a, j'⟩, hF, he⟩ := hadj s h
  rcases pieceEdge_some he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hs] at h1; simp at h1
  · rw [hs] at h1
    simp only [Option.some.injEq, Sum.inr.injEq] at h1
    subst h1
    exact ⟨a, h2, hF, he⟩

theorem f2_edge_l' {F : Finset (A × J)} {p : List (A ⊕ J)}
    (hadj : ∀ i : ℕ, i + 1 < p.length → ∃ e ∈ F, pieceEdge p i = some e)
    {s : ℕ} {j : J} (hs : p[s+1]? = some (Sum.inr j)) :
    ∃ a, p[s]? = some (Sum.inl a) ∧ (a, j) ∈ F ∧ pieceEdge p s = some (a, j) := by
  obtain ⟨⟨a, j'⟩, hF, he⟩ := hadj s (getE hs).1
  rcases pieceEdge_some he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hs] at h2
    simp only [Option.some.injEq, Sum.inr.injEq] at h2
    subst h2
    exact ⟨a, h1, hF, he⟩
  · rw [hs] at h2; simp at h2

theorem f2_same_piece {pieces : List (List (A ⊕ J))}
    (hdisj : pieces.Pairwise (fun p q => ∀ v ∈ p, v ∉ q)) {p q : List (A ⊕ J)}
    (hp : p ∈ pieces) (hq : q ∈ pieces) {v : A ⊕ J} (hvp : v ∈ p) (hvq : v ∈ q) : p = q := by
  by_contra hpq
  haveI : Std.Symm (fun p q : List (A ⊕ J) => ∀ v ∈ p, v ∉ q) :=
    ⟨fun x y h v hv hvx => h v hvx hv⟩
  exact List.Pairwise.forall hdisj hp hq hpq _ hvp hvq

theorem f2_ad_pos {p : List (A ⊕ J)} {i : ℕ} {a : A} {j : J}
    (he : pieceEdge p i = some (a, j)) : ∃ t, p[t]? = some (Sum.inl a) ∧ (t = i ∨ t = i + 1) := by
  rcases pieceEdge_some he with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact ⟨i, h1, Or.inl rfl⟩
  · exact ⟨i + 1, h2, Or.inr rfl⟩

theorem f2_cp_pos {p : List (A ⊕ J)} {i : ℕ} {a : A} {j : J}
    (he : pieceEdge p i = some (a, j)) : ∃ t, p[t]? = some (Sum.inr j) ∧ (t = i ∨ t = i + 1) := by
  rcases pieceEdge_some he with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact ⟨i + 1, h2, Or.inr rfl⟩
  · exact ⟨i, h1, Or.inl rfl⟩

theorem f2_edge_pos {p : List (A ⊕ J)} (hnd : p.Nodup) {i s : ℕ} {a : A} {j : J}
    (he : pieceEdge p i = some (a, j)) (hs : p[s]? = some (Sum.inl a)) : i = s ∨ i + 1 = s := by
  obtain ⟨t, ht, hti⟩ := f2_ad_pos he
  have := f2_nd_pos hnd ht hs
  omega

theorem f2_edge_in {F : Finset (A × J)} {pieces : List (List (A ⊕ J))}
    (hdisj : pieces.Pairwise (fun p q => ∀ v ∈ p, v ∉ q))
    (hcov : ∀ e ∈ F, ∃ p ∈ pieces, ∃ i : ℕ, pieceEdge p i = some e)
    {p : List (A ⊕ J)} (hp : p ∈ pieces) {a : A} {j : J} (hF : (a, j) ∈ F)
    (ha : Sum.inl a ∈ p) : ∃ i, pieceEdge p i = some (a, j) := by
  obtain ⟨q, hq, i, hi⟩ := hcov _ hF
  obtain ⟨t, ht, -⟩ := f2_ad_pos hi
  have : q = p := f2_same_piece hdisj hq hp (List.mem_iff_getElem?.2 ⟨t, ht⟩) ha
  subst this
  exact ⟨i, hi⟩

theorem f2_side {F : Finset (A × J)} {p : List (A ⊕ J)}
    (hadj : ∀ i : ℕ, i + 1 < p.length → ∃ e ∈ F, pieceEdge p i = some e)
    {x : ℕ} {u v0 : A ⊕ J} (hx : p[x]? = some u) (h0 : p[0]? = some v0) :
    (u.isLeft = v0.isLeft ↔ x % 2 = 0) := by
  obtain ⟨hx1, ex⟩ := getE hx
  obtain ⟨h01, e0⟩ := getE h0
  have := side_alt p (fun i hi => by obtain ⟨e, -, he⟩ := hadj i hi; exact ⟨e, he⟩) h01 x hx1
  rw [ex, e0, Nat.even_iff] at this
  exact this

theorem f2_heads {F : Finset (A × J)} {p : List (A ⊕ J)}
    (hadj : ∀ i : ℕ, i + 1 < p.length → ∃ e ∈ F, pieceEdge p i = some e) (hL : 0 < p.length) :
    (∃ b, p[0]? = some (Sum.inl b) ∧ ∀ x (a : A) (j : J),
        (p[x]? = some (Sum.inl a) → x % 2 = 0) ∧ (p[x]? = some (Sum.inr j) → x % 2 = 1)) ∨
    (∃ j0, p[0]? = some (Sum.inr j0) ∧ ∀ x (a : A) (j : J),
        (p[x]? = some (Sum.inl a) → x % 2 = 1) ∧ (p[x]? = some (Sum.inr j) → x % 2 = 0)) := by
  obtain ⟨v0, hv0⟩ : ∃ v0, p[0]? = some v0 := ⟨p[0], List.getElem?_eq_getElem hL⟩
  rcases v0 with b | j0
  · left
    refine ⟨b, hv0, fun x a j => ⟨fun hx => ?_, fun hx => ?_⟩⟩ <;>
      (have := f2_side hadj hx hv0; simp at this; omega)
  · right
    refine ⟨j0, hv0, fun x a j => ⟨fun hx => ?_, fun hx => ?_⟩⟩ <;>
      (have := f2_side hadj hx hv0; simp at this; omega)

theorem f2_blue {blue : Finset (A × J)} {p : List (A ⊕ J)}
    (hblue : ∀ (i : ℕ) (e : A × J), pieceEdge p i = some e →
        (e ∈ blue ↔
          ((p.Nodup ∧ Even (p.length - 1) ∧ ∃ j : J, p.head? = some (Sum.inr j)) ∧
              (i ≤ 1 ∨ Odd i)) ∨
          (¬ (p.Nodup ∧ Even (p.length - 1) ∧ ∃ j : J, p.head? = some (Sum.inr j)) ∧ Even i)))
    (i : ℕ) (e : A × J) (h : pieceEdge p i = some e) :
    (e ∈ blue ↔ (SPp p ∧ (i ≤ 1 ∨ i % 2 = 1)) ∨ (¬ SPp p ∧ i % 2 = 0)) := by
  rw [hblue i e h]
  simp only [SPp, Nat.odd_iff, Nat.even_iff]

theorem f2_int_ad {F : Finset (A × J)} {p : List (A ⊕ J)}
    (hadj : ∀ i : ℕ, i + 1 < p.length → ∃ e ∈ F, pieceEdge p i = some e) (hnd : p.Nodup)
    {s : ℕ} {a : A} (hs : p[s+1]? = some (Sum.inl a)) (h : s + 2 < p.length) :
    2 ≤ adDeg F a := by
  obtain ⟨j1, hj1, hF1, -⟩ := f2_edge_l hadj hs
  obtain ⟨j2, hj2, hF2, -⟩ := f2_edge_r hadj hs (by omega)
  have hne : j1 ≠ j2 := by
    rintro rfl
    have := f2_nd_pos hnd hj1 hj2
    omega
  exact f2_two_le_ad hne hF1 hF2

theorem f2_int_cp {F : Finset (A × J)} {p : List (A ⊕ J)}
    (hadj : ∀ i : ℕ, i + 1 < p.length → ∃ e ∈ F, pieceEdge p i = some e) (hnd : p.Nodup)
    {s : ℕ} {j : J} (hs : p[s+1]? = some (Sum.inr j)) (h : s + 2 < p.length) :
    2 ≤ cpDeg F j := by
  obtain ⟨a1, ha1, hF1, -⟩ := f2_edge_l' hadj hs
  obtain ⟨a2, ha2, hF2, -⟩ := f2_edge_r' hadj hs (by omega)
  have hne : a1 ≠ a2 := by
    rintro rfl
    have := f2_nd_pos hnd ha1 ha2
    omega
  exact f2_two_le_cp hne hF1 hF2

theorem f2_cyc_norm {p : List (A ⊕ J)} (hlen : 5 ≤ p.length) (hhl : p.head? = p.getLast?)
    {t : ℕ} {v : A ⊕ J} (ht : p[t]? = some v) : ∃ t', t' + 1 < p.length ∧ p[t']? = some v := by
  obtain ⟨htl, -⟩ := getE ht
  by_cases h : t + 1 < p.length
  · exact ⟨t, h, ht⟩
  · refine ⟨0, by omega, ?_⟩
    have h1 : p[0]? = p[p.length - 1]? := by
      rw [← List.head?_eq_getElem?, ← List.getLast?_eq_getElem?]; exact hhl
    rw [h1, show p.length - 1 = t by omega]
    exact ht

theorem f2_cyc_ad {F : Finset (A × J)} {p : List (A ⊕ J)}
    (hadj : ∀ i : ℕ, i + 1 < p.length → ∃ e ∈ F, pieceEdge p i = some e)
    (hlen : 5 ≤ p.length) (hhl : p.head? = p.getLast?) (hdl : p.dropLast.Nodup)
    {t : ℕ} {a : A} (ht : p[t]? = some (Sum.inl a)) (htl : t + 1 < p.length) :
    2 ≤ adDeg F a := by
  obtain ⟨j2, hj2, hF2, -⟩ := f2_edge_r hadj ht htl
  have hE : p[p.length - 1]? = p[0]? := by
    rw [← List.head?_eq_getElem?, ← List.getLast?_eq_getElem?]; exact hhl.symm
  obtain ⟨l, hl, j1, hj1, hF1⟩ : ∃ l, (l + 2 = p.length ∧ t = 0 ∨ l + 1 = t) ∧
      ∃ j1, p[l]? = some (Sum.inr j1) ∧ (a, j1) ∈ F := by
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0
      have hlast : p[p.length - 2 + 1]? = some (Sum.inl a) := by
        rw [show p.length - 2 + 1 = p.length - 1 by omega, hE]; exact ht
      obtain ⟨j1, hj1, hF1, -⟩ := f2_edge_l hadj hlast
      exact ⟨_, Or.inl ⟨by omega, rfl⟩, j1, hj1, hF1⟩
    · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
      obtain ⟨j1, hj1, hF1, -⟩ := f2_edge_l hadj ht
      exact ⟨u, Or.inr rfl, j1, hj1, hF1⟩
  have hne : j1 ≠ j2 := by
    rintro rfl
    obtain ⟨hl1, e1⟩ := getE hj1
    obtain ⟨hl2, e2⟩ := getE hj2
    have := pos_cases p hlen hhl hdl l (t+1) hl1 hl2 (e1.trans e2.symm)
    omega
  exact f2_two_le_ad hne hF1 hF2

theorem f2_cyc_cp {F : Finset (A × J)} {p : List (A ⊕ J)}
    (hadj : ∀ i : ℕ, i + 1 < p.length → ∃ e ∈ F, pieceEdge p i = some e)
    (hlen : 5 ≤ p.length) (hhl : p.head? = p.getLast?) (hdl : p.dropLast.Nodup)
    {t : ℕ} {j : J} (ht : p[t]? = some (Sum.inr j)) (htl : t + 1 < p.length) :
    2 ≤ cpDeg F j := by
  obtain ⟨a2, ha2, hF2, -⟩ := f2_edge_r' hadj ht htl
  have hE : p[p.length - 1]? = p[0]? := by
    rw [← List.head?_eq_getElem?, ← List.getLast?_eq_getElem?]; exact hhl.symm
  obtain ⟨l, hl, a1, ha1, hF1⟩ : ∃ l, (l + 2 = p.length ∧ t = 0 ∨ l + 1 = t) ∧
      ∃ a1, p[l]? = some (Sum.inl a1) ∧ (a1, j) ∈ F := by
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0
      have hlast : p[p.length - 2 + 1]? = some (Sum.inr j) := by
        rw [show p.length - 2 + 1 = p.length - 1 by omega, hE]; exact ht
      obtain ⟨a1, ha1, hF1, -⟩ := f2_edge_l' hadj hlast
      exact ⟨_, Or.inl ⟨by omega, rfl⟩, a1, ha1, hF1⟩
    · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
      obtain ⟨a1, ha1, hF1, -⟩ := f2_edge_l' hadj ht
      exact ⟨u, Or.inr rfl, a1, ha1, hF1⟩
  have hne : a1 ≠ a2 := by
    rintro rfl
    obtain ⟨hl1, e1⟩ := getE ha1
    obtain ⟨hl2, e2⟩ := getE ha2
    have := pos_cases p hlen hhl hdl l (t+1) hl1 hl2 (e1.trans e2.symm)
    omega
  exact f2_two_le_cp hne hF1 hF2

theorem f2_cyc_noneg {F blue : Finset (A × J)} (hsub : blue ⊆ F)
    {pieces : List (List (A ⊕ J))}
    (hdisj : pieces.Pairwise (fun p q => ∀ v ∈ p, v ∉ q))
    (hcov : ∀ e ∈ F, ∃ p ∈ pieces, ∃ i : ℕ, pieceEdge p i = some e)
    {p : List (A ⊕ J)} (hp : p ∈ pieces)
    (hadj : ∀ i : ℕ, i + 1 < p.length → ∃ e ∈ F, pieceEdge p i = some e)
    (hlen : 5 ≤ p.length) (hhl : p.head? = p.getLast?) (hdl : p.dropLast.Nodup)
    {a : A} (ha : Sum.inl a ∈ p) (hneg : IsNeg1 F blue a ∨ IsNeg2 F blue a) : False := by
  obtain ⟨t0, ht0⟩ := List.mem_iff_getElem?.1 ha
  obtain ⟨t, htl, ht⟩ := f2_cyc_norm hlen hhl ht0
  have h2 := f2_cyc_ad hadj hlen hhl hdl ht htl
  have cpk : ∀ j, (a, j) ∈ F → 2 ≤ cpDeg F j := by
    intro j hj
    obtain ⟨i, hi⟩ := f2_edge_in hdisj hcov hp hj ha
    obtain ⟨u0, hu0, -⟩ := f2_cp_pos hi
    obtain ⟨u, hul, hu⟩ := f2_cyc_norm hlen hhl hu0
    exact f2_cyc_cp hadj hlen hhl hdl hu hul
  rcases hneg with ⟨h1, -⟩ | ⟨j1, j2, hb1, hF2, -, hd⟩
  · omega
  · rcases hd with hd | hd
    · have := cpk j1 (hsub hb1); omega
    · have := cpk j2 hF2; omega

theorem f2_B_not_neg {F blue : Finset (A × J)} (hsub : blue ⊆ F) {b : A} {j : J}
    (hd : adDeg F b = 1) (hb : (b, j) ∈ blue) : ¬ (IsNeg1 F blue b ∨ IsNeg2 F blue b) := by
  rintro (⟨-, j', hj'F, hj'b⟩ | ⟨j1, j2, hb1, hF2, hr2, -⟩)
  · have hne : j ≠ j' := by rintro rfl; exact hj'b hb
    have := f2_two_le_ad hne (hsub hb) hj'F; omega
  · have hne : j1 ≠ j2 := by rintro rfl; exact hr2 hb1
    have := f2_two_le_ad hne (hsub hb1) hF2; omega

end F2

section F2b
variable {A J : Type} [DecidableEq A] [DecidableEq J]

theorem f2_neg_char {F blue : Finset (A × J)} (hsub : blue ⊆ F) {pieces : List (List (A ⊕ J))}
    (hdisj : pieces.Pairwise (fun p q => ∀ v ∈ p, v ∉ q))
    (hcov : ∀ e ∈ F, ∃ p ∈ pieces, ∃ i : ℕ, pieceEdge p i = some e)
    {p : List (A ⊕ J)} (hp : p ∈ pieces)
    (hadj : ∀ i : ℕ, i + 1 < p.length → ∃ e ∈ F, pieceEdge p i = some e)
    (hnd : p.Nodup) (hL : 2 ≤ p.length)
    (hendA : ∀ x (b : A), p[x]? = some (Sum.inl b) → (x = 0 ∨ x + 1 = p.length) → adDeg F b = 1)
    (hbl : ∀ (i : ℕ) (e : A × J), pieceEdge p i = some e →
        (e ∈ blue ↔ (SPp p ∧ (i ≤ 1 ∨ i % 2 = 1)) ∨ (¬ SPp p ∧ i % 2 = 0)))
    {a : A} {s : ℕ} (hs : p[s]? = some (Sum.inl a)) (hneg : IsNeg1 F blue a ∨ IsNeg2 F blue a) :
    (SPp p ∧ s + 2 = p.length ∧ s ≠ 1 ∧ ¬ IsNeg1 F blue a) ∨
    (¬ SPp p ∧ (∃ b, p[0]? = some (Sum.inl b)) ∧ (p.length - 1) % 2 = 0 ∧ s + 1 = p.length) ∨
    (¬ SPp p ∧ (∃ b, p[0]? = some (Sum.inl b)) ∧ (p.length - 1) % 2 = 1 ∧ s + 2 = p.length) ∨
    (¬ SPp p ∧ (∃ j, p[0]? = some (Sum.inr j)) ∧ (p.length - 1) % 2 = 1 ∧ s = 1) := by
  have hsL : s < p.length := (getE hs).1
  have ha : Sum.inl a ∈ p := List.mem_iff_getElem?.2 ⟨s, hs⟩
  have hspec : ∀ j0 : J, p[0]? = some (Sum.inr j0) → ¬ SPp p → (p.length - 1) % 2 = 1 := by
    intro j0 hj0 hns
    by_contra hc
    exact hns ⟨hnd, Nat.even_iff.2 (by omega), j0, by rw [List.head?_eq_getElem?]; exact hj0⟩
  have hsp1 : SPp p → (∃ j0, p[0]? = some (Sum.inr j0)) ∧ (p.length - 1) % 2 = 0 := by
    rintro ⟨-, hev, j0, hj0⟩
    exact ⟨⟨j0, by rw [← List.head?_eq_getElem?]; exact hj0⟩, Nat.even_iff.1 hev⟩
  have hHL : ∀ b j, p[0]? = some (Sum.inl b) → p[0]? = some (Sum.inr j) → False := by
    intro b j h1 h2; rw [h1] at h2; simp at h2
  rcases hneg with ⟨hd1, j, hjF, hjb⟩ | ⟨j1, j2, hb1, hF2, hr2, hdeg⟩
  · have ends : s = 0 ∨ s + 1 = p.length := by
      by_contra hc
      push_neg at hc
      obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
      have := f2_int_ad (F := F) hadj hnd hs (by omega)
      omega
    obtain ⟨i, hi⟩ := f2_edge_in hdisj hcov hp hjF ha
    have hip := f2_edge_pos hnd hi hs
    have hi1 := mem_of_pieceEdge' hi
    have hred : ¬ ((SPp p ∧ (i ≤ 1 ∨ i % 2 = 1)) ∨ (¬ SPp p ∧ i % 2 = 0)) :=
      fun h => hjb ((hbl i _ hi).2 h)
    rcases f2_heads hadj (by omega) with ⟨b0, hb0, par⟩ | ⟨j0, hj0, par⟩
    · by_cases hsp : SPp p
      · obtain ⟨⟨j0, hj0⟩, -⟩ := hsp1 hsp
        exact (hHL _ _ hb0 hj0).elim
      · simp [hsp] at hred
        right; left
        exact ⟨hsp, ⟨b0, hb0⟩, by omega, by omega⟩
    · have hsA := (par s a j).1 hs
      by_cases hsp : SPp p
      · obtain ⟨-, hev⟩ := hsp1 hsp
        exfalso; omega
      · simp [hsp] at hred
        exfalso; have := hspec j0 hj0 hsp; omega
  · have hF1 := hsub hb1
    have hne : j1 ≠ j2 := by rintro rfl; exact hr2 hb1
    have h2 := f2_two_le_ad hne hF1 hF2
    have hint : 0 < s ∧ s + 1 < p.length := by
      by_contra hc
      have := hendA s a hs (by omega)
      omega
    have aux : ∀ j, (a, j) ∈ F → cpDeg F j = 1 → ∃ t, p[t]? = some (Sum.inr j) ∧
        (t = 0 ∨ t + 1 = p.length) ∧ (t + 1 = s ∨ t = s + 1) := by
      intro j hj hd
      obtain ⟨i, hi⟩ := f2_edge_in hdisj hcov hp hj ha
      have hip := f2_edge_pos hnd hi hs
      obtain ⟨t, ht, hti⟩ := f2_cp_pos hi
      have hts : t ≠ s := by
        rintro rfl; rw [hs] at ht; simp at ht
      have htl : t < p.length := (getE ht).1
      refine ⟨t, ht, ?_, by omega⟩
      by_contra hc
      push_neg at hc
      obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
      have := f2_int_cp (F := F) hadj hnd ht (by omega)
      omega
    obtain ⟨t, jt, ht, ht0, hts⟩ : ∃ t jt, p[t]? = some (Sum.inr jt) ∧
        (t = 0 ∨ t + 1 = p.length) ∧ (t + 1 = s ∨ t = s + 1) := by
      rcases hdeg with hd | hd
      · obtain ⟨t, ht⟩ := aux j1 hF1 hd; exact ⟨t, j1, ht⟩
      · obtain ⟨t, ht⟩ := aux j2 hF2 hd; exact ⟨t, j2, ht⟩
    rcases f2_heads hadj (by omega) with ⟨b0, hb0, par⟩ | ⟨j0, hj0, par⟩
    · have hsA := (par s a jt).1 hs
      have htC := (par t a jt).2 ht
      by_cases hsp : SPp p
      · obtain ⟨⟨j0, hj0⟩, -⟩ := hsp1 hsp
        exact (hHL _ _ hb0 hj0).elim
      · right; right; left
        exact ⟨hsp, ⟨b0, hb0⟩, by omega, by omega⟩
    · have hsA := (par s a jt).1 hs
      have htC := (par t a jt).2 ht
      by_cases hsp : SPp p
      · left
        obtain ⟨-, hev⟩ := hsp1 hsp
        obtain ⟨i2, hi2⟩ := f2_edge_in hdisj hcov hp hF2 ha
        have hip2 := f2_edge_pos hnd hi2 hs
        have hred : ¬ ((SPp p ∧ (i2 ≤ 1 ∨ i2 % 2 = 1)) ∨ (¬ SPp p ∧ i2 % 2 = 0)) :=
          fun h => hr2 ((hbl i2 _ hi2).2 h)
        simp [hsp] at hred
        exact ⟨hsp, by omega, by omega, fun h => by have := h.1; omega⟩
      · right; right; right
        have hsp' := hspec j0 hj0 hsp
        exact ⟨hsp, ⟨j0, hj0⟩, hsp', by omega⟩

theorem f2_neg_uniq {p : List (A ⊕ J)} {s s' : ℕ} {P Q : Prop}
    (h : (SPp p ∧ s + 2 = p.length ∧ s ≠ 1 ∧ P) ∨
      (¬ SPp p ∧ (∃ b, p[0]? = some (Sum.inl b)) ∧ (p.length - 1) % 2 = 0 ∧ s + 1 = p.length) ∨
      (¬ SPp p ∧ (∃ b, p[0]? = some (Sum.inl b)) ∧ (p.length - 1) % 2 = 1 ∧ s + 2 = p.length) ∨
      (¬ SPp p ∧ (∃ j, p[0]? = some (Sum.inr j)) ∧ (p.length - 1) % 2 = 1 ∧ s = 1))
    (h' : (SPp p ∧ s' + 2 = p.length ∧ s' ≠ 1 ∧ Q) ∨
      (¬ SPp p ∧ (∃ b, p[0]? = some (Sum.inl b)) ∧ (p.length - 1) % 2 = 0 ∧ s' + 1 = p.length) ∨
      (¬ SPp p ∧ (∃ b, p[0]? = some (Sum.inl b)) ∧ (p.length - 1) % 2 = 1 ∧ s' + 2 = p.length) ∨
      (¬ SPp p ∧ (∃ j, p[0]? = some (Sum.inr j)) ∧ (p.length - 1) % 2 = 1 ∧ s' = 1)) :
    s = s' := by
  rcases h with ⟨h1, h2, -, -⟩ | ⟨h1, ⟨b, hb⟩, h3, h4⟩ | ⟨h1, ⟨b, hb⟩, h3, h4⟩ |
      ⟨h1, ⟨j, hj⟩, h3, h4⟩ <;>
    rcases h' with ⟨k1, k2, -, -⟩ | ⟨k1, ⟨b', hb'⟩, k3, k4⟩ | ⟨k1, ⟨b', hb'⟩, k3, k4⟩ |
      ⟨k1, ⟨j', hj'⟩, k3, k4⟩ <;>
    first
    | omega
    | exact absurd h1 k1
    | exact absurd k1 h1
    | (rw [hb] at hj'; simp at hj')
    | (rw [hj] at hb'; simp at hb')

theorem f2_partner {F blue : Finset (A × J)} (hsub : blue ⊆ F) {pieces : List (List (A ⊕ J))}
    (hdisj : pieces.Pairwise (fun p q => ∀ v ∈ p, v ∉ q))
    (hcov : ∀ e ∈ F, ∃ p ∈ pieces, ∃ i : ℕ, pieceEdge p i = some e)
    {p : List (A ⊕ J)} (hp : p ∈ pieces)
    (hadj : ∀ i : ℕ, i + 1 < p.length → ∃ e ∈ F, pieceEdge p i = some e)
    (hnd : p.Nodup) (hL : 2 ≤ p.length)
    (hendA : ∀ x (b : A), p[x]? = some (Sum.inl b) → (x = 0 ∨ x + 1 = p.length) → adDeg F b = 1)
    (hbl : ∀ (i : ℕ) (e : A × J), pieceEdge p i = some e →
        (e ∈ blue ↔ (SPp p ∧ (i ≤ 1 ∨ i % 2 = 1)) ∨ (¬ SPp p ∧ i % 2 = 0)))
    {a : A} {s : ℕ}
    (hc : (SPp p ∧ s + 2 = p.length ∧ s ≠ 1 ∧ ¬ IsNeg1 F blue a) ∨
      (¬ SPp p ∧ (∃ b, p[0]? = some (Sum.inl b)) ∧ (p.length - 1) % 2 = 0 ∧ s + 1 = p.length) ∨
      (¬ SPp p ∧ (∃ b, p[0]? = some (Sum.inl b)) ∧ (p.length - 1) % 2 = 1 ∧ s + 2 = p.length) ∨
      (¬ SPp p ∧ (∃ j, p[0]? = some (Sum.inr j)) ∧ (p.length - 1) % 2 = 1 ∧ s = 1)) :
    ∃ b, Sum.inl b ∈ p ∧ (IsBAd F blue b ∨ IsBBAd blue b) ∧ (IsNeg1 F blue a → IsBAd F blue b) ∧
      ¬ (IsNeg1 F blue b ∨ IsNeg2 F blue b) := by
  have endB : ∀ (b : A) x (j : J), p[x]? = some (Sum.inl b) → (x = 0 ∨ x + 1 = p.length) →
      (b, j) ∈ blue →
      ∃ b', Sum.inl b' ∈ p ∧ (IsBAd F blue b' ∨ IsBBAd blue b') ∧
        (IsNeg1 F blue a → IsBAd F blue b') ∧ ¬ (IsNeg1 F blue b' ∨ IsNeg2 F blue b') := by
    intro b x j hx hx0 hbj
    have hd := hendA x b hx hx0
    exact ⟨b, List.mem_iff_getElem?.2 ⟨x, hx⟩, Or.inl ⟨hd, j, hbj⟩, fun _ => ⟨hd, j, hbj⟩,
      f2_B_not_neg hsub hd hbj⟩
  rcases hc with ⟨hsp, hs2, hs1, hn1⟩ | ⟨hsp, ⟨b, hb⟩, -, -⟩ | ⟨hsp, ⟨b, hb⟩, -, -⟩ |
      ⟨hsp, ⟨j0, hj0⟩, hodd, -⟩
  · have hev : (p.length - 1) % 2 = 0 := Nat.even_iff.1 hsp.2.1
    obtain ⟨j0, hj0⟩ := hsp.2.2
    have hj0' : p[0]? = some (Sum.inr j0) := by rw [← List.head?_eq_getElem?]; exact hj0
    have hL5 : 5 ≤ p.length := by omega
    obtain ⟨v1, hv1⟩ : ∃ v1, p[1]? = some v1 := ⟨p[1], List.getElem?_eq_getElem (by omega)⟩
    rcases v1 with b | j1
    · have hb1 : p[0 + 1]? = some (Sum.inl b) := hv1
      obtain ⟨c0, hc0, hF0, he0⟩ := f2_edge_l hadj hb1
      obtain ⟨c2, hc2, hF2, he2⟩ := f2_edge_r hadj hb1 (by omega)
      have bl0 : (b, c0) ∈ blue := (hbl 0 _ he0).2 (Or.inl ⟨hsp, Or.inl (by omega)⟩)
      have bl1 : (b, c2) ∈ blue := (hbl (0 + 1) _ he2).2 (Or.inl ⟨hsp, Or.inl (by omega)⟩)
      have hne : c0 ≠ c2 := by
        rintro rfl; have := f2_nd_pos hnd hc0 hc2; omega
      refine ⟨b, List.mem_iff_getElem?.2 ⟨1, hv1⟩, Or.inr ⟨c0, c2, hne, bl0, bl1⟩,
        fun h => absurd h hn1, ?_⟩
      rintro (⟨hd, -⟩ | ⟨-, c, -, hcF, hcb, -⟩)
      · have := f2_two_le_ad hne hF0 hF2; omega
      · obtain ⟨i, hi⟩ := f2_edge_in hdisj hcov hp hcF (List.mem_iff_getElem?.2 ⟨1, hv1⟩)
        have := f2_edge_pos hnd hi hv1
        exact hcb ((hbl i _ hi).2 (Or.inl ⟨hsp, Or.inl (by omega)⟩))
    · exfalso
      rcases f2_heads hadj (by omega) with ⟨b0, hb0, -⟩ | ⟨j0'', -, par⟩
      · rw [hj0'] at hb0; simp at hb0
      · have := (par 1 a j1).2 hv1; omega
  · obtain ⟨j, -, -, he⟩ := f2_edge_r hadj hb (by omega)
    exact endB b 0 j hb (Or.inl rfl) ((hbl 0 _ he).2 (Or.inr ⟨hsp, by norm_num⟩))
  · obtain ⟨j, -, -, he⟩ := f2_edge_r hadj hb (by omega)
    exact endB b 0 j hb (Or.inl rfl) ((hbl 0 _ he).2 (Or.inr ⟨hsp, by norm_num⟩))
  · obtain ⟨v, hv⟩ : ∃ v, p[p.length - 1]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rcases v with b | jl
    · have hb' : p[p.length - 2 + 1]? = some (Sum.inl b) := by
        rw [show p.length - 2 + 1 = p.length - 1 by omega]; exact hv
      obtain ⟨j, -, -, he⟩ := f2_edge_l hadj hb'
      exact endB b (p.length - 1) j hv (Or.inr (by omega))
        ((hbl _ _ he).2 (Or.inr ⟨hsp, by omega⟩))
    · exfalso
      rcases f2_heads hadj (by omega) with ⟨b0, hb0, -⟩ | ⟨j0'', -, par⟩
      · rw [hj0] at hb0; simp at hb0
      · have := (par _ a jl).2 hv; omega

/-- **F2**: an injection from NEG ads to POS ads (B or BB) of their own piece; NEG1 ads go to
B ads; partners are never NEG. -/
theorem neg_injection {F blue : Finset (A × J)} (hcol : IsTSMColoring F blue) :
    ∃ f : A → A, ∀ a, (IsNeg1 F blue a ∨ IsNeg2 F blue a) →
      (IsBAd F blue (f a) ∨ IsBBAd blue (f a)) ∧ (IsNeg1 F blue a → IsBAd F blue (f a)) ∧
      ¬ (IsNeg1 F blue (f a) ∨ IsNeg2 F blue (f a)) ∧
      ∀ a', (IsNeg1 F blue a' ∨ IsNeg2 F blue a') → f a' = f a → a' = a := by
  obtain ⟨hsub, pieces, hdisj, hcov, hpc⟩ := hcol
  have hloc : ∀ a, ∃ b, (IsNeg1 F blue a ∨ IsNeg2 F blue a) → ∃ p ∈ pieces, Sum.inl a ∈ p ∧
      Sum.inl b ∈ p ∧ (IsBAd F blue b ∨ IsBBAd blue b) ∧ (IsNeg1 F blue a → IsBAd F blue b) ∧
      ¬ (IsNeg1 F blue b ∨ IsNeg2 F blue b) ∧
      ∀ a', (IsNeg1 F blue a' ∨ IsNeg2 F blue a') → Sum.inl a' ∈ p → a' = a := by
    intro a
    by_cases hneg : IsNeg1 F blue a ∨ IsNeg2 F blue a
    swap
    · exact ⟨a, fun h => absurd h hneg⟩
    obtain ⟨j, hj⟩ : ∃ j, (a, j) ∈ F := by
      rcases hneg with ⟨-, j, hj, -⟩ | ⟨-, j, -, hj, -⟩
      · exact ⟨j, hj⟩
      · exact ⟨j, hj⟩
    obtain ⟨p, hp, i, hi⟩ := hcov _ hj
    obtain ⟨t, ht, -⟩ := f2_ad_pos hi
    have ha : Sum.inl a ∈ p := List.mem_iff_getElem?.2 ⟨t, ht⟩
    obtain ⟨hadj, hshape, hblue⟩ := hpc p hp
    have hbl := f2_blue hblue
    rcases hshape with ⟨hnd, hL, hh, hl⟩ | ⟨hlen, hhl, hdl⟩
    swap
    · exact (f2_cyc_noneg hsub hdisj hcov hp hadj hlen hhl hdl ha hneg).elim
    have hendA : ∀ x (b : A), p[x]? = some (Sum.inl b) → (x = 0 ∨ x + 1 = p.length) →
        adDeg F b = 1 := by
      intro x b hx hx'
      rcases hx' with rfl | hx'
      · exact hh (Sum.inl b) (by rw [Option.mem_def, List.head?_eq_getElem?]; exact hx)
      · exact hl (Sum.inl b) (by
          rw [Option.mem_def, List.getLast?_eq_getElem?, show p.length - 1 = x by omega]
          exact hx)
    obtain ⟨s, hs⟩ := List.mem_iff_getElem?.1 ha
    have hc := f2_neg_char hsub hdisj hcov hp hadj hnd hL hendA hbl hs hneg
    obtain ⟨b, hbp, hbB, hb1, hbn⟩ := f2_partner hsub hdisj hcov hp hadj hnd hL hendA hbl hc
    refine ⟨b, fun _ => ⟨p, hp, ha, hbp, hbB, hb1, hbn, ?_⟩⟩
    intro a' hneg' ha'
    obtain ⟨s', hs'⟩ := List.mem_iff_getElem?.1 ha'
    have hc' := f2_neg_char hsub hdisj hcov hp hadj hnd hL hendA hbl hs' hneg'
    have hss := f2_neg_uniq hc' hc
    subst hss
    rw [hs] at hs'
    simp only [Option.some.injEq, Sum.inl.injEq] at hs'
    exact hs'.symm
  choose f hf using hloc
  refine ⟨f, fun a ha => ?_⟩
  obtain ⟨p, hp, hap, hbp, hB, h1, hn, huniq⟩ := hf a ha
  refine ⟨hB, h1, hn, fun a' ha' hfe => ?_⟩
  obtain ⟨p', hp', hap', hbp', -⟩ := hf a' ha'
  rw [hfe] at hbp'
  have : p' = p := f2_same_piece hdisj hp' hp hbp' hbp
  subst this
  exact huniq a' ha' hap'

end F2b

/-- Pairing sum: NEG terms are paired injectively with nonnegative non-NEG partners. -/
theorem sum_pair {ι : Type} [DecidableEq ι] (S : Finset ι) (w : ι → ℝ) (Neg : ι → Prop)
    [DecidablePred Neg] (f : ι → ι)
    (hfS : ∀ a ∈ S, Neg a → f a ∈ S) (hfN : ∀ a ∈ S, Neg a → ¬ Neg (f a))
    (hinj : ∀ a ∈ S, ∀ a' ∈ S, Neg a → Neg a' → f a' = f a → a' = a)
    (hpos : ∀ a ∈ S, ¬ Neg a → 0 ≤ w a) (hpair : ∀ a ∈ S, Neg a → 0 ≤ w a + w (f a)) :
    0 ≤ ∑ a ∈ S, w a := by
  rw [← Finset.sum_filter_add_sum_filter_not S Neg]
  have hT : (S.filter Neg).image f ⊆ S.filter (fun a => ¬ Neg a) := by
    intro b hb
    simp only [Finset.mem_image, Finset.mem_filter] at hb
    obtain ⟨a, ⟨haS, haN⟩, rfl⟩ := hb
    exact Finset.mem_filter.2 ⟨hfS a haS haN, hfN a haS haN⟩
  have h1 : ∑ b ∈ (S.filter Neg).image f, w b ≤ ∑ b ∈ S.filter (fun a => ¬ Neg a), w b :=
    Finset.sum_le_sum_of_subset_of_nonneg hT
      (fun b hb _ => hpos b (Finset.mem_filter.1 hb).1 (Finset.mem_filter.1 hb).2)
  have h2 : ∑ b ∈ (S.filter Neg).image f, w b = ∑ a ∈ S.filter Neg, w (f a) := by
    rw [Finset.sum_image]
    intro a ha a' ha' h
    simp only [Finset.mem_coe, Finset.mem_filter] at ha ha'
    exact hinj a' ha'.1 a ha.1 ha'.2 ha.2 h
  have h3 : 0 ≤ ∑ a ∈ S.filter Neg, (w a + w (f a)) :=
    Finset.sum_nonneg (fun a ha => hpair a (Finset.mem_filter.1 ha).1 (Finset.mem_filter.1 ha).2)
  rw [Finset.sum_add_distrib] at h3
  linarith


/-! ## W (relay 7): edge-weight cover and per-ad local bounds. -/
section W
open Classical TSMnum
variable {A J : Type} [DecidableEq A] [DecidableEq J]

noncomputable def kX (F : Finset (A × J)) (Xa : A → Prop) (j : J) : ℕ :=
  (F.filter (fun e => e.2 = j ∧ Xa e.1)).card
def hasN (F : Finset (A × J)) (Xa : A → Prop) (j : J) : Prop := ∃ a, (a, j) ∈ F ∧ ¬ Xa a
/-- cover weight of an F-edge (transfers folded in). -/
noncomputable def cw (F : Finset (A × J)) (Xa : A → Prop) (Yc : J → Prop) (e : A × J) : ℝ :=
  if Xa e.1 then
    (if Yc e.2 then 1 / 2 else if kX F Xa e.2 = 1 then
      qL - (if hasN F Xa e.2 then tauL / alpha else 0) else rL / 2)
  else 1 / 2 + (if kX F Xa e.2 = 1 then tauL / alpha else 0)
noncomputable def pL (F blue : Finset (A × J)) (a : A) : ℝ :=
  if adDeg F a = 0 then 0 else if adDeg F a = 1 then (if ∃ j, (a, j) ∈ blue then qL else rhoL)
  else if IsBBAd blue a then bbL else bL
noncomputable def wv (F blue : Finset (A × J)) (Xa : A → Prop) (Yc : J → Prop) (a : A) : ℝ :=
  pL F blue a - alpha * ∑ e ∈ F.filter (fun e => e.1 = a), cw F Xa Yc e

theorem ta_eq : alpha * (tauL / alpha) = tauL := by
  have := alpha_pos; field_simp

theorem tau_div_nonneg : 0 ≤ tauL / alpha := div_nonneg n_tau_nonneg alpha_pos.le

theorem cw_XY {F : Finset (A × J)} {Xa : A → Prop} {Yc : J → Prop} {a : A} {j : J}
    (ha : Xa a) (hj : Yc j) : cw F Xa Yc (a, j) = 1 / 2 := by
  unfold cw; rw [if_pos ha, if_pos hj]

theorem cw_X_le {F : Finset (A × J)} {Xa : A → Prop} {Yc : J → Prop} {a : A} {j : J}
    (ha : Xa a) : cw F Xa Yc (a, j) ≤ qL := by
  have h1 := n_half_le_q; have h2 := n_r_le_q; have h5 := tau_div_nonneg
  unfold cw; rw [if_pos ha]
  split_ifs <;> linarith

theorem cw_N_le {F : Finset (A × J)} {Xa : A → Prop} {Yc : J → Prop} {a : A} {j : J}
    (ha : ¬ Xa a) : cw F Xa Yc (a, j) ≤ 1 / 2 + tauL / alpha := by
  have h5 := tau_div_nonneg
  unfold cw; rw [if_neg ha]
  split_ifs <;> linarith

theorem cw_X_nonY_good {F : Finset (A × J)} {Xa : A → Prop} {Yc : J → Prop} {a : A} {j : J}
    (ha : Xa a) (hF : (a, j) ∈ F) (hj : ¬ Yc j) (hc2 : cpDeg F j ≤ 2) (hc : cpDeg F j ≠ 1) :
    cw F Xa Yc (a, j) ≤ rL / 2 ∨ cw F Xa Yc (a, j) = qL - tauL / alpha := by
  unfold cw; rw [if_pos ha, if_neg hj]
  by_cases hk : kX F Xa j = 1
  · right
    rw [if_pos hk]
    have hN : hasN F Xa j := by
      have hpos : 1 ≤ cpDeg F j := Finset.card_pos.2 ⟨(a, j), by simp [hF]⟩
      have hc' : cpDeg F j = 2 := by omega
      unfold cpDeg at hc'
      obtain ⟨x, y, hxy, hxyE⟩ := Finset.card_eq_two.1 hc'
      have hx : x ∈ F.filter (fun e => e.2 = j) := by rw [hxyE]; simp
      have hy : y ∈ F.filter (fun e => e.2 = j) := by rw [hxyE]; simp
      obtain ⟨e, he, hne⟩ : ∃ e ∈ F.filter (fun e => e.2 = j), e ≠ (a, j) := by
        by_cases h : x = (a, j)
        · exact ⟨y, hy, fun h' => hxy (h.trans h'.symm)⟩
        · exact ⟨x, hx, h⟩
      rw [Finset.mem_filter] at he
      refine ⟨e.1, ?_, ?_⟩
      · have : e = (e.1, j) := Prod.ext rfl he.2
        rw [← this]; exact he.1
      · intro hXe
        unfold kX at hk
        obtain ⟨z, hz⟩ := Finset.card_eq_one.1 hk
        have h1 : (a, j) ∈ F.filter (fun e => e.2 = j ∧ Xa e.1) :=
          Finset.mem_filter.2 ⟨hF, rfl, ha⟩
        have h2 : e ∈ F.filter (fun e => e.2 = j ∧ Xa e.1) := Finset.mem_filter.2 ⟨he.1, he.2, hXe⟩
        rw [hz, Finset.mem_singleton] at h1 h2
        exact hne (h2.trans h1.symm)
    rw [if_pos hN]
  · left; rw [if_neg hk]

theorem core2 {F : Finset (A × J)} {Xa : A → Prop} {Yc : J → Prop} {a : A} {jy jo : J}
    (ha : Xa a) (hy : Yc jy) (hFo : (a, jo) ∈ F) (hcd : cpDeg F jo ≤ 2) :
    cw F Xa Yc (a, jy) + cw F Xa Yc (a, jo) ≤ 1 / 2 + qL ∧
    ((Yc jo ∨ cpDeg F jo ≠ 1) → alpha * (cw F Xa Yc (a, jy) + cw F Xa Yc (a, jo)) ≤ bL) := by
  have e1 := cw_XY (F := F) ha hy
  have e2 := cw_X_le (F := F) (Yc := Yc) (j := jo) ha
  refine ⟨by linarith, fun h => ?_⟩
  rw [e1]
  have hal := alpha_pos
  have hab := n_alpha_le_b
  by_cases hj : Yc jo
  · rw [cw_XY ha hj, show (1:ℝ) / 2 + 1 / 2 = 1 by norm_num]; exact hab
  · have hd : cpDeg F jo ≠ 1 := by
      rcases h with h | h
      · exact absurd h hj
      · exact h
    rcases cw_X_nonY_good ha hFo hj hcd hd with h3 | h3
    · have := mul_le_mul_of_nonneg_left (add_le_add_left h3 (1 / 2)) hal.le
      linarith [n_YZ2]
    · rw [h3, show (1:ℝ) / 2 + (qL - tauL / alpha) = (1 / 2 + qL) - tauL / alpha by ring,
        mul_sub, ta_eq]
      linarith [n_YZ1]

theorem filt_one {F : Finset (A × J)} {a : A} (h : adDeg F a = 1) :
    ∃ j, F.filter (fun e => e.1 = a) = {(a, j)} := by
  unfold adDeg at h
  obtain ⟨⟨a', j⟩, hz⟩ := Finset.card_eq_one.1 h
  have : (a', j) ∈ F.filter (fun e => e.1 = a) := by rw [hz]; simp
  have ha' : a' = a := (Finset.mem_filter.1 this).2
  subst ha'
  exact ⟨j, hz⟩

theorem filt_two {F : Finset (A × J)} {a : A} (h : adDeg F a = 2) :
    ∃ j1 j2, j1 ≠ j2 ∧ F.filter (fun e => e.1 = a) = {(a, j1), (a, j2)} := by
  unfold adDeg at h
  obtain ⟨⟨a1, j1⟩, ⟨a2, j2⟩, hne, hz⟩ := Finset.card_eq_two.1 h
  have h1 : (a1, j1) ∈ F.filter (fun e => e.1 = a) := by rw [hz]; simp
  have h2 : (a2, j2) ∈ F.filter (fun e => e.1 = a) := by rw [hz]; simp
  have e1 : a1 = a := (Finset.mem_filter.1 h1).2
  have e2 : a2 = a := (Finset.mem_filter.1 h2).2
  subst e1; subst e2
  exact ⟨j1, j2, fun h => hne (by rw [h]), hz⟩

set_option maxHeartbeats 1000000 in
/-- **W**: local bounds on `w a = pL a - α·load a`. -/
theorem w_bounds {F blue : Finset (A × J)} {Xa : A → Prop} {Yc : J → Prop}
    (hsub : blue ⊆ F) (hd2 : ∀ a, adDeg F a ≤ 2) (hcd2 : ∀ j, cpDeg F j ≤ 2)
    (hN : ∀ a, ¬ Xa a → adDeg F a = 2)
    (hXY : ∀ a, Xa a → adDeg F a = 2 → ∃ j, (a, j) ∈ F ∧ Yc j)
    (hRR : ∀ a j1 j2, j1 ≠ j2 → (a, j1) ∈ F → (a, j1) ∉ blue → (a, j2) ∈ F → (a, j2) ∉ blue →
      False)
    (a : A) :
    (¬ (IsNeg1 F blue a ∨ IsNeg2 F blue a) → 0 ≤ wv F blue Xa Yc a) ∧
    (IsNeg1 F blue a → rhoL - alpha * qL ≤ wv F blue Xa Yc a) ∧
    (IsNeg2 F blue a → bL - alpha * (1 / 2 + qL) ≤ wv F blue Xa Yc a) ∧
    (IsBAd F blue a → qL - alpha * qL ≤ wv F blue Xa Yc a) ∧
    (IsBBAd blue a → bbL - alpha * (1 / 2 + qL) ≤ wv F blue Xa Yc a) := by
  have hal := alpha_pos
  have hal1 := n_alpha_le_one
  have hq := n_half_le_q
  have htau := n_tau_nonneg
  have hYZ1 := n_YZ1
  have hBB := n_BB
  have hbbb := n_b_le_bb
  have htd : 2 * tauL = bL - alpha := by unfold tauL; ring
  have dN2 : IsNeg2 F blue a → 2 ≤ adDeg F a := by
    rintro ⟨j1, j2, hb1, hF2, hr2, -⟩
    exact f2_two_le_ad (by rintro rfl; exact hr2 hb1) (hsub hb1) hF2
  have dBB : IsBBAd blue a → 2 ≤ adDeg F a := by
    rintro ⟨j1, j2, hne, hb1, hb2⟩
    exact f2_two_le_ad hne (hsub hb1) (hsub hb2)
  have hdeg := hd2 a
  unfold wv
  rcases (show adDeg F a = 0 ∨ adDeg F a = 1 ∨ adDeg F a = 2 by omega) with h0 | h1 | h2
  · have hfe : F.filter (fun e => e.1 = a) = ∅ := by
      unfold adDeg at h0; exact Finset.card_eq_zero.1 h0
    have hp : pL F blue a = 0 := by rw [pL, if_pos h0]
    rw [hfe, Finset.sum_empty, hp]
    refine ⟨fun _ => by simp, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have := h.1; omega
    · have := dN2 h; omega
    · have := h.1; omega
    · have := dBB h; omega
  · obtain ⟨j, hfe⟩ := filt_one h1
    have hFj : (a, j) ∈ F := by
      have : (a, j) ∈ F.filter (fun e => e.1 = a) := by rw [hfe]; simp
      exact (Finset.mem_filter.1 this).1
    have hXa : Xa a := by
      by_contra hc; have := hN a hc; omega
    have onlyj : ∀ j', (a, j') ∈ F → j' = j := by
      intro j' hj'
      have : (a, j') ∈ F.filter (fun e => e.1 = a) := Finset.mem_filter.2 ⟨hj', rfl⟩
      rw [hfe] at this; simpa using this
    have hcw := cw_X_le (F := F) (Yc := Yc) (j := j) hXa
    have hm := mul_le_mul_of_nonneg_left hcw hal.le
    rw [hfe, Finset.sum_singleton]
    by_cases hbj : (a, j) ∈ blue
    · have hp : pL F blue a = qL := by
        rw [pL, if_neg (by omega), if_pos h1, if_pos ⟨j, hbj⟩]
      rw [hp]
      refine ⟨fun _ => ?_, fun h => ?_, fun h => ?_, fun _ => ?_, fun h => ?_⟩
      · nlinarith
      · exfalso; obtain ⟨-, j', hj'F, hj'b⟩ := h; rw [onlyj j' hj'F] at hj'b; exact hj'b hbj
      · have := dN2 h; omega
      · linarith
      · have := dBB h; omega
    · have hp : pL F blue a = rhoL := by
        rw [pL, if_neg (by omega), if_pos h1, if_neg]
        rintro ⟨j', hj'⟩; rw [onlyj j' (hsub hj')] at hj'; exact hbj hj'
      rw [hp]
      have hneg1 : IsNeg1 F blue a := ⟨h1, j, hFj, hbj⟩
      refine ⟨fun h => absurd (Or.inl hneg1) h, fun _ => by linarith, fun h => ?_, fun h => ?_,
        fun h => ?_⟩
      · have := dN2 h; omega
      · exfalso; obtain ⟨-, j', hj'⟩ := h; rw [onlyj j' (hsub hj')] at hj'; exact hbj hj'
      · have := dBB h; omega
  · obtain ⟨j1, j2, hne, hfe⟩ := filt_two h2
    have hmem : ∀ j', (a, j') ∈ F → j' = j1 ∨ j' = j2 := by
      intro j' hj'
      have : (a, j') ∈ F.filter (fun e => e.1 = a) := Finset.mem_filter.2 ⟨hj', rfl⟩
      rw [hfe] at this; simpa using this
    have hF1 : (a, j1) ∈ F := by
      have : (a, j1) ∈ F.filter (fun e => e.1 = a) := by rw [hfe]; simp
      exact (Finset.mem_filter.1 this).1
    have hF2 : (a, j2) ∈ F := by
      have : (a, j2) ∈ F.filter (fun e => e.1 = a) := by rw [hfe]; simp
      exact (Finset.mem_filter.1 this).1
    have hpne : (a, j1) ≠ (a, j2) := fun h => hne (congrArg Prod.snd h)
    rw [hfe, Finset.sum_pair hpne]
    have hload : (¬ Xa a → alpha * (cw F Xa Yc (a, j1) + cw F Xa Yc (a, j2)) ≤ alpha + 2 * tauL) ∧
        (Xa a → alpha * (cw F Xa Yc (a, j1) + cw F Xa Yc (a, j2)) ≤ alpha * (1 / 2 + qL)) ∧
        (Xa a → cpDeg F j1 ≠ 1 → cpDeg F j2 ≠ 1 →
          alpha * (cw F Xa Yc (a, j1) + cw F Xa Yc (a, j2)) ≤ bL) := by
      refine ⟨fun hXa => ?_, fun hXa => ?_, fun hXa hd1 hd2' => ?_⟩
      · have e1 := mul_le_mul_of_nonneg_left (cw_N_le (F := F) (Yc := Yc) (j := j1) hXa) hal.le
        have e2 := mul_le_mul_of_nonneg_left (cw_N_le (F := F) (Yc := Yc) (j := j2) hXa) hal.le
        rw [mul_add, ta_eq] at e1 e2
        rw [mul_add]; linarith
      · obtain ⟨j, hjF, hjY⟩ := hXY a hXa h2
        rcases hmem j hjF with rfl | rfl
        · exact mul_le_mul_of_nonneg_left (core2 hXa hjY hF2 (hcd2 j2)).1 hal.le
        · rw [add_comm (cw F Xa Yc (a, j1))]
          exact mul_le_mul_of_nonneg_left (core2 hXa hjY hF1 (hcd2 j1)).1 hal.le
      · obtain ⟨j, hjF, hjY⟩ := hXY a hXa h2
        rcases hmem j hjF with rfl | rfl
        · exact (core2 hXa hjY hF2 (hcd2 j2)).2 (Or.inr hd2')
        · rw [add_comm (cw F Xa Yc (a, j1))]
          exact (core2 hXa hjY hF1 (hcd2 j1)).2 (Or.inr hd1)
    have hN1 : ¬ IsNeg1 F blue a := fun h => by have := h.1; omega
    have hB : ¬ IsBAd F blue a := fun h => by have := h.1; omega
    have nBB : ((a, j1) ∉ blue ∨ (a, j2) ∉ blue) → ¬ IsBBAd blue a := by
      rintro hnb ⟨x, y, hxy, hx, hy⟩
      rcases hmem x (hsub hx) with rfl | rfl <;> rcases hmem y (hsub hy) with rfl | rfl <;>
        first | exact hxy rfl | (rcases hnb with h | h <;> contradiction)
    have split : (IsBBAd blue a ∧ pL F blue a = bbL ∧ ¬ IsNeg2 F blue a) ∨
        (¬ IsBBAd blue a ∧ pL F blue a = bL ∧
          (¬ IsNeg2 F blue a → cpDeg F j1 ≠ 1 ∧ cpDeg F j2 ≠ 1)) := by
      by_cases hb1 : (a, j1) ∈ blue <;> by_cases hb2 : (a, j2) ∈ blue
      · have hBBa : IsBBAd blue a := ⟨j1, j2, hne, hb1, hb2⟩
        refine Or.inl ⟨hBBa, by rw [pL, if_neg (by omega), if_neg (by omega), if_pos hBBa], ?_⟩
        rintro ⟨x, y, -, hyF, hyb, -⟩
        rcases hmem y hyF with rfl | rfl
        · exact hyb hb1
        · exact hyb hb2
      · have hn := nBB (Or.inr hb2)
        refine Or.inr ⟨hn, by rw [pL, if_neg (by omega), if_neg (by omega), if_neg hn], ?_⟩
        intro h2n
        constructor <;> intro hc <;> exact h2n ⟨j1, j2, hb1, hF2, hb2, by omega⟩
      · have hn := nBB (Or.inl hb1)
        refine Or.inr ⟨hn, by rw [pL, if_neg (by omega), if_neg (by omega), if_neg hn], ?_⟩
        intro h2n
        constructor <;> intro hc <;> exact h2n ⟨j2, j1, hb2, hF1, hb1, by omega⟩
      · exact (hRR a j1 j2 hne hF1 hb1 hF2 hb2).elim
    rcases split with ⟨hBBa, hp, hnot2⟩ | ⟨hBBn, hp, hc⟩
    · rw [hp]
      have key : bbL - alpha * (1 / 2 + qL) ≤
          bbL - alpha * (cw F Xa Yc (a, j1) + cw F Xa Yc (a, j2)) := by
        by_cases hXa : Xa a
        · linarith [hload.2.1 hXa]
        · linarith [hload.1 hXa]
      refine ⟨fun _ => by linarith, fun h => absurd h hN1, fun h => absurd h hnot2,
        fun h => absurd h hB, fun _ => key⟩
    · rw [hp]
      have k3 : bL - alpha * (1 / 2 + qL) ≤
          bL - alpha * (cw F Xa Yc (a, j1) + cw F Xa Yc (a, j2)) := by
        by_cases hXa : Xa a
        · linarith [hload.2.1 hXa]
        · linarith [hload.1 hXa]
      refine ⟨fun hn => ?_, fun h => absurd h hN1, fun _ => k3, fun h => absurd h hB,
        fun h => absurd h hBBn⟩
      have hn2 : ¬ IsNeg2 F blue a := fun h => hn (Or.inr h)
      by_cases hXa : Xa a
      · linarith [hload.2.2 hXa (hc hn2).1 (hc hn2).2]
      · linarith [hload.1 hXa]

end W

section W2
open Classical TSMnum
variable {A J : Type} [DecidableEq A] [DecidableEq J]

/-- limit form of C6: `Σ_a w a ≥ 0`, i.e. `Σ_a pL a ≥ α · Σ_{e∈F} cw e`. -/
theorem sum_wv_nonneg [Fintype A] {F blue : Finset (A × J)} {Xa : A → Prop} {Yc : J → Prop}
    (hcol : IsTSMColoring F blue) (hd2 : ∀ a, adDeg F a ≤ 2) (hcd2 : ∀ j, cpDeg F j ≤ 2)
    (hN : ∀ a, ¬ Xa a → adDeg F a = 2)
    (hXY : ∀ a, Xa a → adDeg F a = 2 → ∃ j, (a, j) ∈ F ∧ Yc j) :
    0 ≤ ∑ a, wv F blue Xa Yc a := by
  have hsub : blue ⊆ F := hcol.1
  have hRR : ∀ a j1 j2, j1 ≠ j2 → (a, j1) ∈ F → (a, j1) ∉ blue → (a, j2) ∈ F →
      (a, j2) ∉ blue → False :=
    fun a j1 j2 hne h1 h1' h2 h2' => not_both_red hcol hne h1 h1' h2 h2'
  obtain ⟨f, hf⟩ := neg_injection hcol
  have WB := w_bounds (Xa := Xa) (Yc := Yc) hsub hd2 hcd2 hN hXY hRR
  have hRB := n_RB
  have hN2B := n_NEG2B
  have hN2BB := n_NEG2BB
  have e2 : alpha * (2 * qL) = 2 * (alpha * qL) := by ring
  apply sum_pair Finset.univ (wv F blue Xa Yc) (fun a => IsNeg1 F blue a ∨ IsNeg2 F blue a) f
  · intro a _ _; exact Finset.mem_univ _
  · intro a _ ha; exact (hf a ha).2.2.1
  · intro a _ a' _ ha ha' h; exact (hf a ha).2.2.2 a' ha' h
  · intro a _ ha; exact (WB a).1 ha
  · intro a _ ha
    obtain ⟨hB, h1, -, -⟩ := hf a ha
    by_cases hn1 : IsNeg1 F blue a
    · have u1 := (WB a).2.1 hn1
      have u2 := (WB (f a)).2.2.2.1 (h1 hn1)
      linarith
    · have hn2 : IsNeg2 F blue a := ha.resolve_left hn1
      have u1 := (WB a).2.2.1 hn2
      rcases hB with hB | hB
      · have u2 := (WB (f a)).2.2.2.1 hB; linarith
      · have u2 := (WB (f a)).2.2.2.2 hB; linarith

end W2

section C4

variable {A J : Type} [DecidableEq A] [DecidableEq J]

/-- residual reachability (BFS) from the unsaturated ads, with step count. -/
inductive Rch (E F : Finset (A × J)) : A ⊕ J → ℕ → Prop
  | base (a : A) (h : (F.filter (fun e => e.1 = a)).card < 2) : Rch E F (Sum.inl a) 0
  | toJ (a : A) (j : J) (k : ℕ) (h : Rch E F (Sum.inl a) k) (he : (a, j) ∈ E)
      (hn : (a, j) ∉ F) : Rch E F (Sum.inr j) (k + 1)
  | toA (a : A) (j : J) (k : ℕ) (h : Rch E F (Sum.inr j) k) (hf : (a, j) ∈ F) :
      Rch E F (Sum.inl a) (k + 1)

theorem card_filter_insert_eq (G : Finset (A × J)) (x : A × J) (hx : x ∉ G)
    (P : A × J → Prop) [DecidablePred P] :
    ((insert x G).filter P).card = (G.filter P).card + (if P x then 1 else 0) := by
  rw [Finset.filter_insert]
  by_cases h : P x
  · rw [if_pos h, if_pos h, Finset.card_insert_eq_ite,
      if_neg (fun hm => hx (Finset.mem_filter.1 hm).1)]
  · rw [if_neg h, if_neg h]; rfl

theorem card_filter_swap (G : Finset (A × J)) (x y : A × J) (hy : y ∈ G) (hx : x ∉ G)
    (P : A × J → Prop) [DecidablePred P] :
    ((insert x (G.erase y)).filter P).card + (if P y then 1 else 0) =
      (G.filter P).card + (if P x then 1 else 0) := by
  have hx' : x ∉ G.erase y := fun hm => hx (Finset.mem_of_mem_erase hm)
  rw [card_filter_insert_eq _ x hx' P, Finset.filter_erase]
  by_cases h : P y
  · rw [if_pos h]
    have := Finset.card_erase_add_one (Finset.mem_filter.2 ⟨hy, h⟩)
    omega
  · rw [if_neg h, Finset.erase_eq_self.2 (fun hm => h (Finset.mem_filter.1 hm).2), Nat.add_zero]

theorem augment (E F : Finset (A × J)) (hFE : F ⊆ E) :
    ∀ k : ℕ, ∀ j : J, Rch E F (Sum.inr j) k → (∀ k' < k, ¬ Rch E F (Sum.inr j) k') →
      ∃ G : Finset (A × J), ∃ a0 : A, G ⊆ E ∧ G.card = F.card + 1 ∧
        (F.filter (fun e => e.1 = a0)).card < 2 ∧
        (G.filter (fun e => e.1 = a0)).card ≤ (F.filter (fun e => e.1 = a0)).card + 1 ∧
        (∀ a, a ≠ a0 → (G.filter (fun e => e.1 = a)).card ≤ (F.filter (fun e => e.1 = a)).card) ∧
        (G.filter (fun e => e.2 = j)).card ≤ (F.filter (fun e => e.2 = j)).card + 1 ∧
        (∀ j', j' ≠ j → (G.filter (fun e => e.2 = j')).card ≤ (F.filter (fun e => e.2 = j')).card) ∧
        (∀ a' : A, (∀ k' ≤ k, ¬ Rch E F (Sum.inl a') k') → ∀ j' : J,
          ((a', j') ∈ G ↔ (a', j') ∈ F)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro j hj hmin
  cases hj with
  | toJ a _ k1 ha he hn =>
    have hamin : ∀ k'' < k1, ¬ Rch E F (Sum.inl a) k'' := fun k'' hk h =>
      hmin (k'' + 1) (by omega) (Rch.toJ a j k'' h he hn)
    cases ha with
    | base _ hdeg =>
      refine ⟨insert (a, j) F, a, Finset.insert_subset_iff.2 ⟨he, hFE⟩, ?_, hdeg, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_eq_ite, if_neg hn]
      · rw [card_filter_insert_eq F _ hn]; split_ifs <;> omega
      · intro a' ha'
        rw [card_filter_insert_eq F _ hn, if_neg (fun h => ha' h.symm)]; omega
      · rw [card_filter_insert_eq F _ hn]; split_ifs <;> omega
      · intro j' hj'
        rw [card_filter_insert_eq F _ hn, if_neg (fun h => hj' h.symm)]; omega
      · intro a' ha' j'
        have hne : a' ≠ a := fun h => ha' 0 (by omega) (h ▸ Rch.base a hdeg)
        rw [Finset.mem_insert]
        constructor
        · rintro (h | h)
          · exact absurd (congrArg Prod.fst h) hne
          · exact h
        · exact fun h => Or.inr h
    | toA _ j0 k0 hj0 hf =>
      have hj0min : ∀ k'' < k0, ¬ Rch E F (Sum.inr j0) k'' := fun k'' hk h =>
        hamin (k'' + 1) (by omega) (Rch.toA a j0 k'' h hf)
      obtain ⟨G0, a0, hsub, hcard, hdeg0, hA0, hA, hJ0, hJ, hag⟩ :=
        ih k0 (by omega) j0 hj0 hj0min
      have haun : ∀ k' ≤ k0, ¬ Rch E F (Sum.inl a) k' := fun k' hk => hamin k' (by omega)
      have hy : (a, j0) ∈ G0 := (hag a haun j0).2 hf
      have hx : (a, j) ∉ G0 := fun h => hn ((hag a haun j).1 h)
      have hjj0 : j ≠ j0 := fun h => hn (h ▸ hf)
      have hxy : (a, j) ≠ (a, j0) := fun h => hjj0 (congrArg Prod.snd h)
      refine ⟨insert (a, j) (G0.erase (a, j0)), a0, ?_, ?_, hdeg0, ?_, ?_, ?_, ?_, ?_⟩
      · exact Finset.insert_subset_iff.2 ⟨he, (Finset.erase_subset _ _).trans hsub⟩
      · have h1 := Finset.card_erase_add_one hy
        rw [Finset.card_insert_eq_ite,
          if_neg (fun hm => hx (Finset.mem_of_mem_erase hm))]
        omega
      · have := card_filter_swap G0 (a, j) (a, j0) hy hx (fun e => e.1 = a0)
        simp only at this
        split_ifs at this <;> omega
      · intro a' ha'
        have := card_filter_swap G0 (a, j) (a, j0) hy hx (fun e => e.1 = a')
        simp only at this
        have := hA a' ha'
        split_ifs at * <;> omega
      · have := card_filter_swap G0 (a, j) (a, j0) hy hx (fun e => e.2 = j)
        simp only at this
        rw [if_neg hjj0.symm] at this
        simp only [eq_self_iff_true, ↓reduceIte] at this
        have := hJ j hjj0
        omega
      · intro j' hj'
        have h1 := card_filter_swap G0 (a, j) (a, j0) hy hx (fun e => e.2 = j')
        simp only at h1
        rw [if_neg (show ¬ (j = j') from fun h => hj' h.symm)] at h1
        by_cases h2 : j' = j0
        · rw [if_pos (show j0 = j' from h2.symm)] at h1
          subst h2
          have := hJ0
          omega
        · rw [if_neg (show ¬ (j0 = j') from fun h => h2 h.symm)] at h1
          have := hJ j' h2
          omega
      · intro a' ha' j'
        have hne : a' ≠ a := fun h => ha' (k0 + 1) (by omega) (h ▸ Rch.toA a j0 k0 hj0 hf)
        have hag' := hag a' (fun k' hk => ha' k' (by omega)) j'
        rw [Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro (h | ⟨-, h⟩)
          · exact absurd (congrArg Prod.fst h) hne
          · exact hag'.1 h
        · exact fun h => Or.inr ⟨fun h' => hne (congrArg Prod.fst h'), hag'.2 h⟩

/-- C4 key fact: every reachable copy is saturated by a maximum 2-matching. -/
theorem Y_sat (E F : Finset (A × J)) (hF : IsMaxTwoMatching E F) (j : J) (k : ℕ)
    (h : Rch E F (Sum.inr j) k) : (F.filter (fun e => e.2 = j)).card = 2 := by
  classical
  have hex : ∃ k, Rch E F (Sum.inr j) k := ⟨k, h⟩
  obtain ⟨G, a0, hsub, hcard, hdeg0, hA0, hA, hJ0, hJ, -⟩ :=
    augment E F hF.1.1 (Nat.find hex) j (Nat.find_spec hex) (fun k' hk' => Nat.find_min hex hk')
  by_contra hne
  have hle := hF.1.2.2 j
  have hG : IsTwoMatching E G := by
    refine ⟨hsub, fun a => ?_, fun j' => ?_⟩
    · by_cases ha : a = a0
      · subst ha; omega
      · exact (hA a ha).trans (hF.1.2.1 a)
    · by_cases hj' : j' = j
      · subst hj'; omega
      · exact (hJ j' hj').trans (hF.1.2.2 j')
  have := hF.2 G hG
  omega

/-! Cut structure facts (X = reachable ads, Y = reachable copies). -/

theorem rch_ad_of_F (E F : Finset (A × J)) {a : A} {j : J} {k : ℕ}
    (hj : Rch E F (Sum.inr j) k) (hf : (a, j) ∈ F) : Rch E F (Sum.inl a) (k + 1) :=
  Rch.toA a j k hj hf

theorem rch_copy_of_nonF (E F : Finset (A × J)) {a : A} {j : J} {k : ℕ}
    (ha : Rch E F (Sum.inl a) k) (he : (a, j) ∈ E) (hn : (a, j) ∉ F) :
    Rch E F (Sum.inr j) (k + 1) :=
  Rch.toJ a j k ha he hn

/-- unreachable ads are saturated. -/
theorem N_sat (E F : Finset (A × J)) (hF : IsMaxTwoMatching E F) (a : A)
    (ha : ∀ k, ¬ Rch E F (Sum.inl a) k) : (F.filter (fun e => e.1 = a)).card = 2 := by
  have h2 := hF.1.2.1 a
  by_contra hne
  exact ha 0 (Rch.base a (by omega))

/-- a reachable saturated ad has an F-neighbour among the reachable copies. -/
theorem X_has_Y (E F : Finset (A × J)) {a : A} {k : ℕ} (ha : Rch E F (Sum.inl a) k)
    (h2 : (F.filter (fun e => e.1 = a)).card = 2) :
    ∃ j k', (a, j) ∈ F ∧ Rch E F (Sum.inr j) k' := by
  cases ha with
  | base _ h => omega
  | toA _ j k' hj hf => exact ⟨j, k', hf, hj⟩

end C4

section C5

/-- C5 pointwise: a copy-level cover `(T, S)` bounds the realized OPT. -/
theorem realOPT_le_cover {A I J : Type} [Fintype A] [DecidableEq A] [DecidableEq I]
    [DecidableEq J] {n : ℕ} (E : Finset (A × I)) (π : J → I) (κ : Fin n → J)
    (T : Finset A) (S : Finset J)
    (hcov : ∀ (a : A) (t : Fin n), (a, π (κ t)) ∈ E → a ∈ T ∨ κ t ∈ S) :
    realOPT E (fun t => π (κ t)) ≤ T.card + ∑ j ∈ S,
      min (Finset.univ.filter (fun t => κ t = j)).card
        (Finset.univ.filter (fun a => a ∉ T ∧ (a, π j) ∈ E)).card := by
  classical
  unfold realOPT
  apply Finset.sup_le
  intro M hM
  rw [Finset.mem_filter] at hM
  obtain ⟨-, hE, h1, h2⟩ := hM
  rw [← Finset.card_filter_add_card_filter_not (s := M) (fun p : A × Fin n => p.1 ∈ T)]
  apply add_le_add
  · apply Finset.card_le_card_of_injOn (fun p => p.1)
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp
      exact hp.2
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      exact h1 p hp.1 q hq.1 hpq
  · have hmap : ∀ p ∈ M.filter (fun p : A × Fin n => ¬ p.1 ∈ T), κ p.2 ∈ S := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rcases hcov p.1 p.2 (hE p hp.1) with h | h
      · exact absurd h hp.2
      · exact h
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    apply Finset.sum_le_sum
    intro j _
    apply le_min
    · apply Finset.card_le_card_of_injOn (fun p => p.2)
      · intro p hp
        simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq] at hp
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
        exact hp.2
      · intro p hp q hq hpq
        simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq] at hp hq
        exact h2 p hp.1.1 q hq.1.1 hpq
    · apply Finset.card_le_card_of_injOn (fun p => p.1)
      · intro p hp
        simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq] at hp
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
        refine ⟨hp.1.2, ?_⟩
        have := hE p hp.1.1
        simp only at this
        rw [hp.2] at this
        exact this
      · intro p hp q hq hpq
        simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq] at hp hq
        exact h1 p hp.1.1 q hq.1.1 hpq

end C5
section OPTC
open Classical

/-- pointwise cover bound for the copy instance: `T = N`, `S = all copies`; a non-`Y` copy's
`X`-neighbours in `copyEdges` are its `F`-neighbours in `X`. -/
theorem opt_cover {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (E : Finset (A × I)) (e : I → ℕ) (F : Finset (A × Copy e)) (Xa : A → Prop)
    (Yc : Copy e → Prop)
    (hZ : ∀ a j, Xa a → (a, j) ∈ copyEdges E e → (a, j) ∉ F → Yc j)
    {n : ℕ} (ω : Fin n → Copy e) :
    (realOPT E (fun t => (ω t).1) : ℝ) ≤
      ((Finset.univ.filter (fun a => ¬ Xa a)).card : ℝ) +
        ∑ j, (if Yc j then ((Finset.univ.filter (fun t => ω t = j)).card : ℝ) else
          ((min (Finset.univ.filter (fun t => ω t = j)).card (kX F Xa j) : ℕ) : ℝ)) := by
  have h := realOPT_le_cover E (fun j : Copy e => j.1) ω
    (Finset.univ.filter (fun a => ¬ Xa a)) Finset.univ
    (fun _ t _ => Or.inr (Finset.mem_univ (ω t)))
  have h' : (realOPT E (fun t => (ω t).1) : ℝ) ≤
      (((Finset.univ.filter (fun a => ¬ Xa a)).card + ∑ j ∈ (Finset.univ : Finset (Copy e)),
        min (Finset.univ.filter (fun t => ω t = j)).card
          (Finset.univ.filter (fun a => a ∉ Finset.univ.filter (fun a => ¬ Xa a) ∧
            (a, j.1) ∈ E)).card : ℕ) : ℝ) := by exact_mod_cast h
  refine h'.trans ?_
  push_cast
  refine add_le_add le_rfl (Finset.sum_le_sum ?_)
  intro j _
  by_cases hy : Yc j
  · rw [if_pos hy]; exact_mod_cast min_le_left _ _
  · rw [if_neg hy]
    have hd : (Finset.univ.filter (fun a => a ∉ Finset.univ.filter (fun a => ¬ Xa a) ∧
        (a, j.1) ∈ E)).card ≤ kX F Xa j := by
      unfold kX
      apply Finset.card_le_card_of_injOn (fun a => (a, j))
      · intro a ha
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Finset.mem_filter,
          not_not, Set.mem_setOf_eq] at ha ⊢
        refine ⟨?_, ha.1⟩
        by_contra hn
        exact hy (hZ a j ha.1 (by unfold copyEdges; simpa using ha.2) hn)
      · intro a _ b _ hab
        simp only [Prod.mk.injEq] at hab
        exact hab.1
    have := min_le_min_left (Finset.univ.filter (fun t => ω t = j)).card hd
    exact_mod_cast this

end OPTC

section DC
open Classical TSMnum
variable {A J : Type} [DecidableEq A] [DecidableEq J]

/-- limit of `E[min(cnt_j, k)]` (k ≤ 2). -/
noncomputable def muL (k : ℕ) : ℝ := if k = 0 then 0 else if k = 1 then qL else rL

theorem dc_mem {F : Finset (A × J)} {e : A × J} {j : J} (he : e ∈ F) (h : e.2 = j) :
    (e.1, j) ∈ F := by rw [← h]; exact he

/-- per-copy part of the cover weight (N-edges pay 1/2 to their ad). -/
theorem copy_part {F : Finset (A × J)} {Xa : A → Prop} {Yc : J → Prop} (j : J)
    (ht : 0 ≤ tauL / alpha) (hr : 0 ≤ rL)
    (hY : Yc j → cpDeg F j = 2 ∧ ∀ a, (a, j) ∈ F → Xa a) :
    (if Yc j then (1:ℝ) else muL (kX F Xa j)) ≤
      ∑ e ∈ F.filter (fun e => e.2 = j),
        (cw F Xa Yc e - if Xa e.1 then (0:ℝ) else 1 / 2) := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun e : A × J => Xa e.1)]
  have hfX : (F.filter (fun e => e.2 = j)).filter (fun e => Xa e.1) =
      F.filter (fun e => e.2 = j ∧ Xa e.1) := by
    rw [Finset.filter_filter]
  rw [hfX]
  have hNt : ∀ e ∈ (F.filter (fun e => e.2 = j)).filter (fun e => ¬ Xa e.1),
      cw F Xa Yc e - (if Xa e.1 then (0:ℝ) else 1 / 2) =
        if kX F Xa j = 1 then tauL / alpha else 0 := by
    intro e he
    rw [Finset.mem_filter, Finset.mem_filter] at he
    unfold cw
    rw [if_neg he.2, if_neg he.2, he.1.2]
    ring
  have hNnn : 0 ≤ ∑ e ∈ (F.filter (fun e => e.2 = j)).filter (fun e => ¬ Xa e.1),
      (cw F Xa Yc e - if Xa e.1 then (0:ℝ) else 1 / 2) := by
    apply Finset.sum_nonneg
    intro e he
    rw [hNt e he]
    split_ifs
    · exact ht
    · exact le_refl _
  by_cases hy : Yc j
  · obtain ⟨h2, hall⟩ := hY hy
    have hk : F.filter (fun e => e.2 = j ∧ Xa e.1) = F.filter (fun e => e.2 = j) := by
      apply Finset.filter_congr
      intro e he
      exact ⟨fun h => h.1, fun h => ⟨h, hall e.1 (dc_mem he h)⟩⟩
    have hXt : ∀ e ∈ F.filter (fun e => e.2 = j ∧ Xa e.1),
        cw F Xa Yc e - (if Xa e.1 then (0:ℝ) else 1 / 2) = 1 / 2 := by
      intro e he
      rw [Finset.mem_filter] at he
      unfold cw
      rw [if_pos he.2.2, if_pos he.2.2, he.2.1, if_pos hy]
      ring
    rw [Finset.sum_congr rfl hXt, Finset.sum_const, hk, if_pos hy]
    unfold cpDeg at h2
    rw [h2]
    norm_num at hNnn ⊢
    linarith
  · rw [if_neg hy]
    set k := kX F Xa j with hkdef
    have hXt : ∀ e ∈ F.filter (fun e => e.2 = j ∧ Xa e.1),
        cw F Xa Yc e - (if Xa e.1 then (0:ℝ) else 1 / 2) =
          if k = 1 then qL - (if hasN F Xa j then tauL / alpha else 0) else rL / 2 := by
      intro e he
      rw [Finset.mem_filter] at he
      unfold cw
      rw [if_pos he.2.2, if_pos he.2.2, he.2.1, if_neg hy]
      ring
    rw [Finset.sum_congr rfl hXt, Finset.sum_const]
    have hcard : (F.filter (fun e => e.2 = j ∧ Xa e.1)).card = k := rfl
    rw [hcard, nsmul_eq_mul]
    unfold muL
    by_cases h0 : k = 0
    · rw [if_pos h0, h0]; simp only [Nat.cast_zero, zero_mul, zero_add]; exact hNnn
    rw [if_neg h0]
    by_cases h1 : k = 1
    · rw [if_pos h1, if_pos h1, h1]
      by_cases hn : hasN F Xa j
      · rw [if_pos hn]
        obtain ⟨a, haF, haX⟩ := hn
        have hmem : (a, j) ∈ (F.filter (fun e => e.2 = j)).filter (fun e => ¬ Xa e.1) := by
          rw [Finset.mem_filter, Finset.mem_filter]; exact ⟨⟨haF, rfl⟩, haX⟩
        have hle := Finset.single_le_sum (f := fun e => cw F Xa Yc e -
          (if Xa e.1 then (0:ℝ) else 1 / 2)) (fun e he => by
            show 0 ≤ cw F Xa Yc e - (if Xa e.1 then (0:ℝ) else 1 / 2)
            rw [hNt e he]; split_ifs <;> first | exact ht | exact le_refl _) hmem
        simp only at hle
        rw [hNt _ hmem, if_pos h1] at hle
        push_cast
        linarith
      · rw [if_neg hn]; push_cast; linarith
    · rw [if_neg h1, if_neg h1]
      have hk2 : (2:ℝ) ≤ k := by exact_mod_cast (by omega : 2 ≤ k)
      nlinarith

/-- double counting (iii): the cover bound `|N| + Σ_j (Y:1 | Z:μ(k_j))` is at most `Σ_{e∈F} cw e`. -/
theorem sum_cw_ge [Fintype A] [Fintype J] {F : Finset (A × J)} {Xa : A → Prop} {Yc : J → Prop}
    (ht : 0 ≤ tauL / alpha) (hr : 0 ≤ rL)
    (hN : ∀ a, ¬ Xa a → adDeg F a = 2)
    (hY : ∀ j, Yc j → cpDeg F j = 2 ∧ ∀ a, (a, j) ∈ F → Xa a) :
    ((Finset.univ.filter (fun a => ¬ Xa a)).card : ℝ) +
        ∑ j, (if Yc j then (1:ℝ) else muL (kX F Xa j)) ≤ ∑ e ∈ F, cw F Xa Yc e := by
  set g : A × J → ℝ := fun e => if Xa e.1 then (0:ℝ) else 1 / 2 with hg
  have h1 : ∑ e ∈ F, cw F Xa Yc e = ∑ e ∈ F, (cw F Xa Yc e - g e) + ∑ e ∈ F, g e := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro e _; ring
  have h2 : ∑ e ∈ F, g e = ((Finset.univ.filter (fun a => ¬ Xa a)).card : ℝ) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := Finset.univ)
      (fun e _ => Finset.mem_univ e.1)]
    have hper : ∀ a : A, ∑ e ∈ F.filter (fun e => e.1 = a), g e =
        if ¬ Xa a then (1:ℝ) else 0 := by
      intro a
      have hc : ∀ e ∈ F.filter (fun e => e.1 = a), g e = if Xa a then (0:ℝ) else 1 / 2 := by
        intro e he; rw [Finset.mem_filter] at he; rw [hg]; simp only; rw [he.2]
      rw [Finset.sum_congr rfl hc, Finset.sum_const]
      by_cases hx : Xa a
      · rw [if_pos hx, if_neg (not_not.2 hx)]; simp
      · rw [if_neg hx, if_pos hx]
        have := hN a hx
        unfold adDeg at this
        rw [this]; norm_num
    rw [Finset.sum_congr rfl (fun a _ => hper a), Finset.sum_boole]
  have h3 : ∑ e ∈ F, (cw F Xa Yc e - g e) =
      ∑ j, ∑ e ∈ F.filter (fun e => e.2 = j), (cw F Xa Yc e - g e) :=
    (Finset.sum_fiberwise_of_maps_to (g := Prod.snd) (t := Finset.univ)
      (fun e _ => Finset.mem_univ e.2) _).symm
  rw [h1, h2, h3, add_comm]
  refine add_le_add (Finset.sum_le_sum ?_) le_rfl
  intro j _
  exact copy_part j ht hr (hY j)
end DC

/-! ## ALG side (relay 9): per-ad hit probabilities. -/
section ALGside
open TSMnum FMMMProof
variable {A J : Type} [DecidableEq A] [DecidableEq J]

/-- no copy carries two red edges. -/
theorem cp_not_both_red {F blue : Finset (A × J)} (hcol : IsTSMColoring F blue)
    {j : J} {a1 a2 : A} (hne : a1 ≠ a2) (h1 : (a1, j) ∈ F) (h1' : (a1, j) ∉ blue)
    (h2 : (a2, j) ∈ F) (h2' : (a2, j) ∉ blue) : False := by
  obtain ⟨-, pieces, hdisj, hcov, hpc⟩ := hcol
  obtain ⟨p, hp, i, hi⟩ := hcov _ h1
  obtain ⟨q, hq, i', hi'⟩ := hcov _ h2
  have memJ : ∀ (r : List (A ⊕ J)) (k : ℕ) (aa : A), pieceEdge r k = some (aa, j) →
      Sum.inr j ∈ r := by
    intro r k aa h
    rcases pieceEdge_some h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact List.mem_iff_getElem?.2 ⟨_, h2⟩
    · exact List.mem_iff_getElem?.2 ⟨_, h1⟩
  have hpq : p = q := by
    by_contra hpq
    haveI : Std.Symm (fun p q : List (A ⊕ J) => ∀ v ∈ p, v ∉ q) :=
      ⟨fun x y h v hv hvx => h v hvx hv⟩
    exact List.Pairwise.forall hdisj hp hq hpq _ (memJ p i a1 hi) (memJ q i' a2 hi')
  subst hpq
  obtain ⟨-, hshape, hblue⟩ := hpc p hp
  have hii : i ≠ i' := by
    rintro rfl
    rw [hi] at hi'
    exact hne (congrArg Prod.fst (Option.some.inj hi'))
  have posJ : ∀ (k : ℕ) (aa : A), pieceEdge p k = some (aa, j) →
      ∃ s, (s = k ∨ s = k + 1) ∧ ∃ hs : s < p.length, p[s] = Sum.inr j := by
    intro k aa h
    rcases pieceEdge_some h with ⟨_, h2⟩ | ⟨h1, _⟩
    · obtain ⟨hs, e⟩ := getE h2
      exact ⟨k + 1, Or.inr rfl, hs, e⟩
    · obtain ⟨hs, e⟩ := getE h1
      exact ⟨k, Or.inl rfl, hs, e⟩
  obtain ⟨s, hs, hsl, es⟩ := posJ i a1 hi
  obtain ⟨s', hs', hsl', es'⟩ := posJ i' a2 hi'
  have r1 := red_parity (F := F) hblue hi h1'
  have r2 := red_parity (F := F) hblue hi' h2'
  have cons : s = s' → False := by
    intro hss
    by_cases hsp : (p.Nodup ∧ Even (p.length - 1) ∧ ∃ j : J, p.head? = some (Sum.inr j))
    · obtain ⟨-, ⟨x1, hx1⟩⟩ := r1.1 hsp
      obtain ⟨-, ⟨x2, hx2⟩⟩ := r2.1 hsp
      omega
    · obtain ⟨x1, hx1⟩ := r1.2 hsp
      obtain ⟨x2, hx2⟩ := r2.2 hsp
      omega
  rcases hshape with ⟨hnd, -, -, -⟩ | ⟨hlen, hhl, hdl⟩
  · exact cons ((List.Nodup.getElem_inj_iff hnd).1 (es.trans es'.symm))
  · have hnn : ¬ p.Nodup := by
      intro hnd
      have h1 : p[0]? = p[p.length - 1]? := by
        rw [← List.head?_eq_getElem?, ← List.getLast?_eq_getElem?]; exact hhl
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
      have := (List.Nodup.getElem_inj_iff hnd).1 (Option.some.inj h1)
      omega
    have hsp : ¬ (p.Nodup ∧ Even (p.length - 1) ∧ ∃ j : J, p.head? = some (Sum.inr j)) :=
      fun h => hnn h.1
    obtain ⟨x1, hx1⟩ := r1.2 hsp
    obtain ⟨x2, hx2⟩ := r2.2 hsp
    rcases pos_cases p hlen hhl hdl s s' hsl hsl' (es.trans es'.symm) with h | h | h
    · exact cons h
    · omega
    · omega

/-- no copy carries two blue edges. -/
theorem cp_not_both_blue {F blue : Finset (A × J)} (hcol : IsTSMColoring F blue)
    {j : J} {a1 a2 : A} (hne : a1 ≠ a2) (h1 : (a1, j) ∈ blue) (h2 : (a2, j) ∈ blue) : False := by
  obtain ⟨hsub, pieces, hdisj, hcov, hpc⟩ := hcol
  obtain ⟨p, hp, i, hi⟩ := hcov _ (hsub h1)
  obtain ⟨q, hq, i', hi'⟩ := hcov _ (hsub h2)
  have memJ : ∀ (r : List (A ⊕ J)) (k : ℕ) (aa : A), pieceEdge r k = some (aa, j) →
      Sum.inr j ∈ r := by
    intro r k aa h
    rcases pieceEdge_some h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact List.mem_iff_getElem?.2 ⟨_, h2⟩
    · exact List.mem_iff_getElem?.2 ⟨_, h1⟩
  have hpq : p = q := by
    by_contra hpq
    haveI : Std.Symm (fun p q : List (A ⊕ J) => ∀ v ∈ p, v ∉ q) :=
      ⟨fun x y h v hv hvx => h v hvx hv⟩
    exact List.Pairwise.forall hdisj hp hq hpq _ (memJ p i a1 hi) (memJ q i' a2 hi')
  subst hpq
  obtain ⟨hadj, hshape, hblue⟩ := hpc p hp
  have hii : i ≠ i' := by
    rintro rfl
    rw [hi] at hi'
    exact hne (congrArg Prod.fst (Option.some.inj hi'))
  have posJ : ∀ (k : ℕ) (aa : A), pieceEdge p k = some (aa, j) →
      ∃ s, (s = k ∨ s = k + 1) ∧ ∃ hs : s < p.length, p[s] = Sum.inr j := by
    intro k aa h
    rcases pieceEdge_some h with ⟨_, h2⟩ | ⟨h1, _⟩
    · obtain ⟨hs, e⟩ := getE h2
      exact ⟨k + 1, Or.inr rfl, hs, e⟩
    · obtain ⟨hs, e⟩ := getE h1
      exact ⟨k, Or.inl rfl, hs, e⟩
  obtain ⟨s, hs, hsl, es⟩ := posJ i a1 hi
  obtain ⟨s', hs', hsl', es'⟩ := posJ i' a2 hi'
  have b1 := (hblue i _ hi).1 h1
  have b2 := (hblue i' _ hi').1 h2
  have hl1 := mem_of_pieceEdge' hi
  have hl2 := mem_of_pieceEdge' hi'
  -- the position-1 vertex of a piece headed by a copy is an ad
  have p1 : (∃ j0 : J, p.head? = some (Sum.inr j0)) → (i = 0 ∨ i' = 0) → s = 1 → False := by
    rintro ⟨j0, hj0⟩ h0 hs1
    have hp0 : p[0]? = some (Sum.inr j0) := by rw [← List.head?_eq_getElem?]; exact hj0
    have hp1 : p[1]? = some (Sum.inr j) := by
      rw [List.getElem?_eq_getElem (by omega)]; subst hs1; exact congrArg some es
    rcases h0 with h0 | h0
    · subst h0
      rcases pieceEdge_some hi with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [hp0] at h1; cases h1
      · rw [hp1] at h2; cases h2
    · subst h0
      rcases pieceEdge_some hi' with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [hp0] at h1; cases h1
      · rw [hp1] at h2; cases h2
  have cons : s = s' → False := by
    intro hss
    by_cases hsp : (p.Nodup ∧ Even (p.length - 1) ∧ ∃ j : J, p.head? = some (Sum.inr j))
    · have c1 := b1.elim (fun h => h.2) (fun h => absurd h.1 (not_not.2 hsp))
      have c2 := b2.elim (fun h => h.2) (fun h => absurd h.1 (not_not.2 hsp))
      have key : s = 1 ∧ (i = 0 ∨ i' = 0) := by
        rcases c1 with c1 | ⟨x1, hx1⟩ <;> rcases c2 with c2 | ⟨x2, hx2⟩ <;> omega
      exact p1 hsp.2.2 key.2 key.1
    · obtain ⟨x1, hx1⟩ := b1.elim (fun h => absurd h.1 hsp) (fun h => h.2)
      obtain ⟨x2, hx2⟩ := b2.elim (fun h => absurd h.1 hsp) (fun h => h.2)
      omega
  rcases hshape with ⟨hnd, -, -, -⟩ | ⟨hlen, hhl, hdl⟩
  · exact cons ((List.Nodup.getElem_inj_iff hnd).1 (es.trans es'.symm))
  · have hnn : ¬ p.Nodup := by
      intro hnd
      have h1 : p[0]? = p[p.length - 1]? := by
        rw [← List.head?_eq_getElem?, ← List.getLast?_eq_getElem?]; exact hhl
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
      have := (List.Nodup.getElem_inj_iff hnd).1 (Option.some.inj h1)
      omega
    have hsp : ¬ (p.Nodup ∧ Even (p.length - 1) ∧ ∃ j : J, p.head? = some (Sum.inr j)) :=
      fun h => hnn h.1
    obtain ⟨x1, hx1⟩ := b1.elim (fun h => absurd h.1 hsp) (fun h => h.2)
    obtain ⟨x2, hx2⟩ := b2.elim (fun h => absurd h.1 hsp) (fun h => h.2)
    -- the cycle has an even number of edges
    have hadj' : ∀ k : ℕ, k + 1 < p.length → ∃ e, pieceEdge p k = some e := by
      intro k hk; obtain ⟨e, -, he⟩ := hadj k hk; exact ⟨e, he⟩
    have E0 : p[0] = p[p.length - 1] := by
      have h1 : p[0]? = p[p.length - 1]? := by
        rw [← List.head?_eq_getElem?, ← List.getLast?_eq_getElem?]; exact hhl
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
      exact Option.some.inj h1
    have hev : Even (p.length - 1) :=
      (side_alt p hadj' (by omega) (p.length - 1) (by omega)).1 (by rw [← E0])
    obtain ⟨y, hy⟩ := hev
    rcases pos_cases p hlen hhl hdl s s' hsl hsl' (es.trans es'.symm) with h | h | h
    · exact cons h
    · omega
    · omega

theorem blue_uniq {F blue : Finset (A × J)} (hcol : IsTSMColoring F blue) {a : A} {j : J}
    (h : (a, j) ∈ blue) : ∀ a', (a', j) ∈ blue → a' = a := by
  intro a' h'
  by_contra hne
  exact cp_not_both_blue hcol hne h' h

theorem red_uniq {F blue : Finset (A × J)} (hcol : IsTSMColoring F blue) {a : A} {j : J}
    (h : (a, j) ∈ F \ blue) : ∀ a', (a', j) ∈ F \ blue → a' = a := by
  intro a' h'
  by_contra hne
  rw [Finset.mem_sdiff] at h h'
  exact cp_not_both_red hcol hne h'.1 h'.2 h.1 h.2

/-- uniform finite-`n` error. -/
noncomputable def errN (n : ℕ) : ℝ := Real.exp (2 / n) - 1

theorem errN_nonneg (n : ℕ) : 0 ≤ errN n := by
  unfold errN; have := Real.one_le_exp (show (0:ℝ) ≤ 2 / n by positivity); linarith

theorem err1_le (n : ℕ) : x * (Real.exp (1 / n) - 1) ≤ errN n := by
  unfold errN
  have hb := x_bounds
  have h1 : Real.exp (1 / n) ≤ Real.exp (2 / n) := by
    apply Real.exp_le_exp.2; gcongr; norm_num
  have h2 := Real.one_le_exp (show (0:ℝ) ≤ 1 / n by positivity)
  nlinarith

theorem err2_le (n : ℕ) : x ^ 2 * (Real.exp (2 / n) - 1) ≤ errN n := by
  have hb := x_bounds
  have h0 := errN_nonneg n
  unfold errN at h0 ⊢
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  nlinarith

theorem errN_le (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) * errN n ≤ 2 * Real.exp 2 := by
  unfold errN
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn
  set y : ℝ := 2 / n with hydef
  have hy0 : 0 ≤ y := by positivity
  have hy2 : y ≤ 2 := by rw [hydef, div_le_iff₀ (by linarith)]; linarith
  have hny : (n:ℝ) * y = 2 := by rw [hydef]; field_simp
  have h1 := Real.add_one_le_exp (-y)
  have h2 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  have hp : 0 < Real.exp y := Real.exp_pos y
  have h3 : Real.exp y - 1 ≤ Real.exp y * y := by nlinarith
  have h4 : Real.exp y ≤ Real.exp 2 := Real.exp_le_exp.2 hy2
  calc (n:ℝ) * (Real.exp y - 1) ≤ (n:ℝ) * (Real.exp y * y) := by gcongr
    _ = 2 * Real.exp y := by rw [mul_comm (Real.exp y), ← mul_assoc, hny]
    _ ≤ 2 * Real.exp 2 := by linarith

theorem exp_neg_two : Real.exp (-2) = x ^ 2 := by
  unfold x; rw [← Real.exp_nat_mul]; norm_num

theorem good_ge {Ω : Type} [Fintype Ω] (P Q : Ω → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ ω, ¬ P ω → Q ω) (β : ℝ) (hQ : ((Finset.univ.filter Q).card : ℝ) ≤ β) :
    (Fintype.card Ω : ℝ) - β ≤ ((Finset.univ.filter P).card : ℝ) := by
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ) P
  have h2 : (Finset.univ.filter (fun ω => ¬ P ω)).card ≤ (Finset.univ.filter Q).card := by
    apply Finset.card_le_card
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact hPQ ω hω
  rw [Finset.card_univ] at h1
  have h1' : ((Finset.univ.filter P).card : ℝ) + (Finset.univ.filter (fun ω => ¬ P ω)).card =
      Fintype.card Ω := by exact_mod_cast h1
  have h2' : ((Finset.univ.filter (fun ω => ¬ P ω)).card : ℝ) ≤ (Finset.univ.filter Q).card := by
    exact_mod_cast h2
  linarith

theorem cnt_pos_of {n : ℕ} {ω : Fin n → J} {j : J} {t : Fin n} (ht : ω t = j) :
    1 ≤ (Finset.univ.filter (fun t => ω t = j)).card :=
  Finset.card_pos.2 ⟨t, by simp [ht]⟩

/-- an ad of degree 2 with one blue and one red edge is hit w.p. ≥ bL - err. -/
theorem alg_mixed [Fintype J] {F blue : Finset (A × J)} (hcol : IsTSMColoring F blue)
    (n : ℕ) (hN : Fintype.card J = n) {a : A} {jb jr : J} (hne : jb ≠ jr)
    (hb : (a, jb) ∈ blue) (hr : (a, jr) ∈ F \ blue) :
    (n : ℝ) ^ n * bL - (n : ℝ) ^ n * errN n ≤
      ((Finset.univ.filter (fun ω : Fin n → J => a ∈ FMMM.TSM.tsmRun blue (F \ blue) ω)).card : ℝ) := by
  have hcard : ((Fintype.card (Fin n → J) : ℕ) : ℝ) = (n:ℝ) ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, hN]; push_cast; ring
  have hj : jr ∉ ({jb} : Finset J) := by simpa using hne.symm
  have key := good_ge (fun ω : Fin n → J => a ∈ FMMM.TSM.tsmRun blue (F \ blue) ω)
    (fun ω => (∀ t, ω t ∉ ({jb} : Finset J)) ∧
      (Finset.univ.filter (fun t => ω t = jr)).card ≤ 1) ?_ _
    (avoid_cnt_le_exp n hN {jb} jr hj)
  · have hc : ((({jb} : Finset J).card : ℕ) : ℝ) + 1 = 2 := by
      rw [Finset.card_singleton]; norm_num
    rw [hc, hcard, exp_neg_two] at key
    have he := err2_le n
    have hP : 0 ≤ (n:ℝ) ^ n := by positivity
    have hm : (n:ℝ) ^ n * (x ^ 2 * (Real.exp (2 / n) - 1)) ≤ (n:ℝ) ^ n * errN n :=
      mul_le_mul_of_nonneg_left he hP
    have e1 : (n:ℝ) ^ n * (x ^ 2 * (1 + Real.exp (2 / n))) =
        (n:ℝ) ^ n * (2 * x ^ 2) + (n:ℝ) ^ n * (x ^ 2 * (Real.exp (2 / n) - 1)) := by ring
    have e2 : (n:ℝ) ^ n * bL = (n:ℝ) ^ n - (n:ℝ) ^ n * (2 * x ^ 2) := by unfold bL; ring
    linarith
  · intro ω hnot
    refine ⟨fun t ht => hnot (mem_alg_blue hb (blue_uniq hcol hb) (cnt_pos_of (by simpa using ht))), ?_⟩
    by_contra hc
    exact hnot (mem_alg_red hr (red_uniq hcol hr) (by omega))

set_option maxHeartbeats 1000000 in
/-- per-ad hit count (all degrees ≤ 2). -/
theorem alg_ad_ge [Fintype J] {F blue : Finset (A × J)} (hcol : IsTSMColoring F blue)
    (n : ℕ) (hN : Fintype.card J = n) (a : A) (hd : adDeg F a ≤ 2) :
    (n : ℝ) ^ n * pL F blue a - (n : ℝ) ^ n * (if adDeg F a = 0 then 0 else errN n) ≤
      ((Finset.univ.filter (fun ω : Fin n → J => a ∈ FMMM.TSM.tsmRun blue (F \ blue) ω)).card : ℝ) := by
  have hcard : ((Fintype.card (Fin n → J) : ℕ) : ℝ) = (n:ℝ) ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, hN]; push_cast; ring
  have hP : 0 ≤ (n:ℝ) ^ n := by positivity
  have hE := errN_nonneg n
  have hEm : 0 ≤ (n:ℝ) ^ n * errN n := mul_nonneg hP hE
  have hsub := hcol.1
  by_cases h0 : adDeg F a = 0
  · rw [if_pos h0]; unfold pL; rw [if_pos h0]; simp
  rw [if_neg h0]
  rcases (show adDeg F a = 1 ∨ adDeg F a = 2 by omega) with hd1 | hd2
  · have hd1' := hd1
    unfold adDeg at hd1'
    obtain ⟨⟨a', j⟩, he⟩ := Finset.card_eq_one.1 hd1'
    have hmem : (a', j) ∈ F.filter (fun e => e.1 = a) := by rw [he]; exact Finset.mem_singleton_self _
    obtain ⟨heF, hea⟩ := Finset.mem_filter.1 hmem
    simp only at hea
    rw [hea] at heF
    by_cases hb : (a, j) ∈ blue
    · have hpl : pL F blue a = qL := by
        unfold pL; rw [if_neg h0, if_pos hd1, if_pos ⟨j, hb⟩]
      have key := good_ge (fun ω : Fin n → J => a ∈ FMMM.TSM.tsmRun blue (F \ blue) ω)
        (fun ω => ∀ t, ω t ∉ ({j} : Finset J)) ?_ _ (avoid_le_exp n hN {j})
      · rw [Finset.card_singleton, hcard, Nat.cast_one] at key
        have hx : Real.exp (-1) = x := rfl
        rw [hx] at key
        have e2 : (n:ℝ) ^ n * pL F blue a = (n:ℝ) ^ n - (n:ℝ) ^ n * x := by
          rw [hpl]; unfold qL; ring
        linarith
      · intro ω hnot t ht
        exact hnot (mem_alg_blue hb (blue_uniq hcol hb) (cnt_pos_of (by simpa using ht)))
    · have hr : (a, j) ∈ F \ blue := Finset.mem_sdiff.2 ⟨heF, hb⟩
      have hnb : ¬ ∃ j', (a, j') ∈ blue := by
        rintro ⟨j', hj'⟩
        have : (a, j') ∈ F.filter (fun e => e.1 = a) := Finset.mem_filter.2 ⟨hsub hj', rfl⟩
        rw [he, Finset.mem_singleton] at this
        rw [hea] at this
        exact hb (by rw [← this]; exact hj')
      have hpl : pL F blue a = rhoL := by
        unfold pL; rw [if_neg h0, if_pos hd1, if_neg hnb]
      have key := good_ge (fun ω : Fin n → J => a ∈ FMMM.TSM.tsmRun blue (F \ blue) ω)
        (fun ω => (∀ t, ω t ∉ (∅ : Finset J)) ∧
          (Finset.univ.filter (fun t => ω t = j)).card ≤ 1) ?_ _
        (avoid_cnt_le_exp n hN ∅ j (Finset.notMem_empty j))
      · have hc : (((∅ : Finset J).card : ℕ) : ℝ) + 1 = 1 := by
          rw [Finset.card_empty]; norm_num
        rw [hc, hcard] at key
        have hx : Real.exp (-1) = x := rfl
        rw [hx] at key
        have he1 := err1_le n
        have hm : (n:ℝ) ^ n * (x * (Real.exp (1 / n) - 1)) ≤ (n:ℝ) ^ n * errN n :=
          mul_le_mul_of_nonneg_left he1 hP
        have e1 : (n:ℝ) ^ n * (x * (1 + Real.exp (1 / n))) =
            (n:ℝ) ^ n * (2 * x) + (n:ℝ) ^ n * (x * (Real.exp (1 / n) - 1)) := by ring
        have e2 : (n:ℝ) ^ n * pL F blue a = (n:ℝ) ^ n - (n:ℝ) ^ n * (2 * x) := by
          rw [hpl]; unfold rhoL; ring
        linarith
      · intro ω hnot
        refine ⟨fun t => Finset.notMem_empty _, ?_⟩
        by_contra hc
        exact hnot (mem_alg_red hr (red_uniq hcol hr) (by omega))
  · have hd2' := hd2
    unfold adDeg at hd2'
    obtain ⟨⟨a1, j1⟩, ⟨a2, j2⟩, hne, he⟩ := Finset.card_eq_two.1 hd2'
    have m1 : (a1, j1) ∈ F.filter (fun e => e.1 = a) := by rw [he]; simp
    have m2 : (a2, j2) ∈ F.filter (fun e => e.1 = a) := by rw [he]; simp
    obtain ⟨f1, ha1⟩ := Finset.mem_filter.1 m1
    obtain ⟨f2, ha2⟩ := Finset.mem_filter.1 m2
    simp only at ha1 ha2
    rw [ha1] at f1 hne he
    rw [ha2] at f2 hne he
    have hj : j1 ≠ j2 := fun h => hne (by rw [h])
    have honly : ∀ j', (a, j') ∈ F → j' = j1 ∨ j' = j2 := by
      intro j' hj'
      have : (a, j') ∈ F.filter (fun e => e.1 = a) := Finset.mem_filter.2 ⟨hj', rfl⟩
      rw [he] at this
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, true_and] at this
      exact this
    by_cases b1 : (a, j1) ∈ blue <;> by_cases b2 : (a, j2) ∈ blue
    · have hbb : IsBBAd blue a := ⟨j1, j2, hj, b1, b2⟩
      have hnot1 : pL F blue a = bbL := by
        unfold pL; rw [if_neg h0, if_neg (by omega : ¬ adDeg F a = 1), if_pos hbb]
      have key := good_ge (fun ω : Fin n → J => a ∈ FMMM.TSM.tsmRun blue (F \ blue) ω)
        (fun ω => ∀ t, ω t ∉ ({j1, j2} : Finset J)) ?_ _ (avoid_le_exp n hN {j1, j2})
      · have hc : ((({j1, j2} : Finset J).card : ℕ) : ℝ) = 2 := by
          rw [Finset.card_pair hj]; norm_num
        rw [hc, hcard, exp_neg_two] at key
        have e2 : (n:ℝ) ^ n * pL F blue a = (n:ℝ) ^ n - (n:ℝ) ^ n * x ^ 2 := by
          rw [hnot1]; unfold bbL; ring
        linarith
      · intro ω hnot t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with ht | ht
        · exact hnot (mem_alg_blue b1 (blue_uniq hcol b1) (cnt_pos_of ht))
        · exact hnot (mem_alg_blue b2 (blue_uniq hcol b2) (cnt_pos_of ht))
    · have hnbb : ¬ IsBBAd blue a := by
        rintro ⟨k1, k2, hk, hk1, hk2⟩
        rcases honly k1 (hsub hk1) with r1 | r1 <;> rcases honly k2 (hsub hk2) with r2 | r2
        · exact hk (r1.trans r2.symm)
        · exact b2 (r2 ▸ hk2)
        · exact b2 (r1 ▸ hk1)
        · exact hk (r1.trans r2.symm)
      have hnot1 : pL F blue a = bL := by
        unfold pL; rw [if_neg h0, if_neg (by omega : ¬ adDeg F a = 1), if_neg hnbb]
      rw [hnot1]
      exact alg_mixed hcol n hN hj b1 (Finset.mem_sdiff.2 ⟨f2, b2⟩)
    · have hnbb : ¬ IsBBAd blue a := by
        rintro ⟨k1, k2, hk, hk1, hk2⟩
        rcases honly k1 (hsub hk1) with r1 | r1 <;> rcases honly k2 (hsub hk2) with r2 | r2
        · exact hk (r1.trans r2.symm)
        · exact b1 (r1 ▸ hk1)
        · exact b1 (r2 ▸ hk2)
        · exact hk (r1.trans r2.symm)
      have hnot1 : pL F blue a = bL := by
        unfold pL; rw [if_neg h0, if_neg (by omega : ¬ adDeg F a = 1), if_neg hnbb]
      rw [hnot1]
      exact alg_mixed hcol n hN hj.symm b2 (Finset.mem_sdiff.2 ⟨f1, b1⟩)
    · exact absurd (not_both_red hcol hj f1 b1 f2 b2) id

/-- summed ALG side: Σ_ω |ALG| ≥ n^n (Σ_a pL a - errN·|F|). -/
theorem sum_alg_ge [Fintype A] [Fintype J] {F blue : Finset (A × J)}
    (hcol : IsTSMColoring F blue) (n : ℕ) (hN : Fintype.card J = n)
    (hd : ∀ a, adDeg F a ≤ 2) :
    (n : ℝ) ^ n * (∑ a, pL F blue a) - (n : ℝ) ^ n * (errN n * F.card) ≤
      ∑ ω : Fin n → J, ((FMMM.TSM.tsmRun blue (F \ blue) ω).card : ℝ) := by
  set T := fun ω : Fin n → J => FMMM.TSM.tsmRun blue (F \ blue) ω with hT
  have hsw : ∑ ω : Fin n → J, ((T ω).card : ℝ) =
      ∑ a, ((Finset.univ.filter (fun ω : Fin n → J => a ∈ T ω)).card : ℝ) := by
    have h1 : ∀ ω, ((T ω).card : ℝ) = ∑ a, if a ∈ T ω then (1:ℝ) else 0 := by
      intro ω
      rw [Finset.sum_boole]
      congr 2; ext a; simp
    have h2 : ∀ a, ((Finset.univ.filter (fun ω : Fin n → J => a ∈ T ω)).card : ℝ) =
        ∑ ω : Fin n → J, if a ∈ T ω then (1:ℝ) else 0 := by
      intro a; rw [Finset.sum_boole]
    simp_rw [h1, h2]
    exact Finset.sum_comm
  have hdeg : ∑ a, (if adDeg F a = 0 then (0:ℝ) else 1) ≤ F.card := by
    have hF : F.card = ∑ a, adDeg F a := by
      unfold adDeg
      exact Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ x.1)
    rw [hF]; push_cast
    apply Finset.sum_le_sum
    intro a _
    split_ifs with h
    · positivity
    · have : 1 ≤ adDeg F a := by omega
      exact_mod_cast this
  have hP : 0 ≤ (n:ℝ) ^ n := by positivity
  have hE := errN_nonneg n
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset A)) =>
    alg_ad_ge hcol n hN a (hd a))
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hite : ∑ a, (if adDeg F a = 0 then (0:ℝ) else errN n) =
      errN n * ∑ a, (if adDeg F a = 0 then (0:ℝ) else 1) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; split_ifs <;> simp
  rw [hite] at hsum
  have hm : (n:ℝ) ^ n * (errN n * ∑ a, (if adDeg F a = 0 then (0:ℝ) else 1)) ≤
      (n:ℝ) ^ n * (errN n * F.card) := by
    apply mul_le_mul_of_nonneg_left _ hP
    exact mul_le_mul_of_nonneg_left hdeg hE
  rw [hsw]
  linarith

end ALGside


/-! ## E-combination (relay 9): α Σ_ω OPT ≤ Σ_ω ALG + n^n (α + errN·|F|). -/
section Ecomb
open Classical TSMnum

theorem muE_eq (k : ℕ) : muE k = muL k := by
  unfold muE muL qL rL x; rfl

theorem rL_nonneg : 0 ≤ rL := by have hb := x_bounds; unfold rL; linarith

theorem e_combine {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (E : Finset (A × I)) (e : I → ℕ) (F blue : Finset (A × Copy e))
    (hF : IsMaxTwoMatching (copyEdges E e) F) (hcol : IsTSMColoring F blue)
    (n : ℕ) (hN : Fintype.card (Copy e) = n) (hn : 0 < n) :
    alpha * ∑ ω : Fin n → Copy e, (realOPT E (fun t => (ω t).1) : ℝ) ≤
      ∑ ω : Fin n → Copy e, ((tsmRun blue (F \ blue) ω).card : ℝ) +
        (n : ℝ) ^ n * (alpha + errN n * F.card) := by
  set G := copyEdges E e with hG
  let Xa : A → Prop := fun a => ∃ k, Rch G F (Sum.inl a) k
  let Yc : Copy e → Prop := fun j => ∃ k, Rch G F (Sum.inr j) k
  have hd2 : ∀ a, adDeg F a ≤ 2 := fun a => hF.1.2.1 a
  have hcd2 : ∀ j, cpDeg F j ≤ 2 := fun j => hF.1.2.2 j
  have hNs : ∀ a, ¬ Xa a → adDeg F a = 2 := by
    intro a ha
    exact N_sat G F hF a (fun k hk => ha ⟨k, hk⟩)
  have hY : ∀ j, Yc j → cpDeg F j = 2 ∧ ∀ a, (a, j) ∈ F → Xa a := by
    rintro j ⟨k, hk⟩
    exact ⟨Y_sat G F hF j k hk, fun a ha => ⟨k + 1, rch_ad_of_F G F hk ha⟩⟩
  have hXY : ∀ a, Xa a → adDeg F a = 2 → ∃ j, (a, j) ∈ F ∧ Yc j := by
    rintro a ⟨k, hk⟩ h2
    obtain ⟨j, k', hj, hk'⟩ := X_has_Y G F hk h2
    exact ⟨j, hj, k', hk'⟩
  have hZ : ∀ a j, Xa a → (a, j) ∈ G → (a, j) ∉ F → Yc j := by
    rintro a j ⟨k, hk⟩ he hn
    exact ⟨k + 1, rch_copy_of_nonF G F hk he hn⟩
  have hkX : ∀ j, kX F Xa j ≤ 2 := by
    intro j
    refine le_trans (Finset.card_le_card ?_) (hcd2 j)
    intro e he; simp only [Finset.mem_filter] at he ⊢; exact ⟨he.1, he.2.1⟩
  have hcard : ((Fintype.card (Fin n → Copy e) : ℕ) : ℝ) = (n:ℝ) ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, hN]; push_cast; ring
  have hP : 0 ≤ (n:ℝ) ^ n := by positivity
  have hα : 0 ≤ alpha := alpha_pos.le
  -- OPT side
  have h3 := Finset.sum_le_sum (fun ω (_ : ω ∈ (Finset.univ : Finset (Fin n → Copy e))) =>
    opt_cover E e F Xa Yc hZ ω)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard] at h3
  have h2 := sum_cover_le n hN hn Yc (kX F Xa) hkX
  simp only [muE_eq] at h2
  have h4 := sum_cw_ge (F := F) (Xa := Xa) (Yc := Yc) tau_div_nonneg rL_nonneg hNs hY
  -- weights
  have h5 := sum_wv_nonneg (blue := blue) (Xa := Xa) (Yc := Yc) hcol hd2 hcd2 hNs hXY
  unfold wv at h5
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := Finset.univ)
      (fun e _ => Finset.mem_univ e.1)] at h5
  -- ALG side
  have h6 := sum_alg_ge hcol n hN hd2
  set SO := ∑ ω : Fin n → Copy e, (realOPT E (fun t => (ω t).1) : ℝ)
  set NN := ((Finset.univ.filter (fun a => ¬ Xa a)).card : ℝ)
  set Sy := ∑ j, (if Yc j then (1:ℝ) else muL (kX F Xa j))
  set C := ∑ e ∈ F, cw F Xa Yc e
  set L := ∑ a, pL F blue a
  have h3' : SO ≤ (n:ℝ) ^ n * NN + (n:ℝ) ^ n * (Sy + 1) := le_trans h3 (by linarith)
  have m1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hP) hα
  have m2 := mul_le_mul_of_nonneg_left (show alpha * C ≤ L by linarith) hP
  calc alpha * SO ≤ alpha * ((n:ℝ) ^ n * NN + (n:ℝ) ^ n * (Sy + 1)) :=
        mul_le_mul_of_nonneg_left h3' hα
    _ = alpha * ((n:ℝ) ^ n * (NN + Sy)) + (n:ℝ) ^ n * alpha := by ring
    _ ≤ alpha * ((n:ℝ) ^ n * C) + (n:ℝ) ^ n * alpha := by linarith
    _ = (n:ℝ) ^ n * (alpha * C) + (n:ℝ) ^ n * alpha := by ring
    _ ≤ (n:ℝ) ^ n * L + (n:ℝ) ^ n * alpha := by linarith
    _ ≤ _ := by
      have e1 : (n:ℝ) ^ n * (alpha + errN n * F.card) =
          (n:ℝ) ^ n * alpha + (n:ℝ) ^ n * (errN n * F.card) := by ring
      linarith

end Ecomb

section C7
open TSMnum FMMMProof

theorem unifProb_mono' {Ω : Type} [Fintype Ω] (n : ℕ) (P Q : (Fin n → Ω) → Prop)
    (h : ∀ ω, P ω → Q ω) : unifProb Ω n P ≤ unifProb Ω n Q := by
  classical
  unfold unifProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (fun ω hω => by
    simp only [Finset.mem_filter] at hω ⊢; exact ⟨hω.1, h ω hω.2⟩)

theorem unifProb_le_one' {Ω : Type} [Fintype Ω] (n : ℕ) (P : (Fin n → Ω) → Prop) :
    unifProb Ω n P ≤ 1 := by
  classical
  unfold unifProb
  apply div_le_one_of_le₀ _ (by positivity)
  have h1 := Finset.card_filter_le (Finset.univ : Finset (Fin n → Ω)) P
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h1
  exact_mod_cast h1

theorem F_card_le {A J : Type} [DecidableEq A] [Fintype J] [DecidableEq J]
    {E F : Finset (A × J)} (hF : IsTwoMatching E F) :
    (F.card : ℝ) ≤ 2 * (Fintype.card J : ℝ) := by
  have h : F.card = ∑ j : J, (F.filter (fun e => e.2 = j)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ x.2)
  have h2 : ∑ j : J, (F.filter (fun e => e.2 = j)).card ≤ ∑ _j : J, 2 :=
    Finset.sum_le_sum (fun j _ => hF.2.2 j)
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h2
  have h3 : F.card ≤ 2 * Fintype.card J := by omega
  exact_mod_cast h3

theorem avg_bound {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (E : Finset (A × I)) (e : I → ℕ) (F blue : Finset (A × Copy e))
    (hF : IsMaxTwoMatching (copyEdges E e) F) (hcol : IsTSMColoring F blue)
    (n : ℕ) (hN : Fintype.card (Copy e) = n) (hn : 0 < n) :
    alpha * avg n (fun ω : Fin n → Copy e => (realOPT E (fun t => (ω t).1) : ℝ)) ≤
      avg n (fun ω : Fin n → Copy e => ((tsmRun blue (F \ blue) ω).card : ℝ)) +
        (1 + 4 * Real.exp 2) := by
  have hc := e_combine E e F blue hF hcol n hN hn
  have hpos : (0:ℝ) < (n:ℝ) ^ n := by positivity
  have hFc := F_card_le hF.1
  rw [hN] at hFc
  have herr := errN_le n hn
  have herr0 := errN_nonneg n
  have hal := n_alpha_le_one
  have hk : errN n * (F.card : ℝ) ≤ 4 * Real.exp 2 := by
    calc errN n * (F.card : ℝ) ≤ errN n * (2 * n) := mul_le_mul_of_nonneg_left hFc herr0
      _ = 2 * ((n:ℝ) * errN n) := by ring
      _ ≤ 2 * (2 * Real.exp 2) := by linarith
      _ = 4 * Real.exp 2 := by ring
  have hd : ((Fintype.card (Copy e) : ℕ) : ℝ) ^ n = (n:ℝ) ^ n := by rw [hN]
  unfold avg
  rw [hd]
  have key := div_le_div_of_nonneg_right hc hpos.le
  rw [add_div, mul_div_cancel_left₀ _ hpos.ne', mul_div_assoc] at key
  linarith

theorem c7_core (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c) (N0 : ℕ)
    (hN0 : 4 * (1 + 4 * Real.exp 2) / (ε * c) < N0)
    {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (E : Finset (A × I)) (e : I → ℕ) (F blue : Finset (A × Copy e))
    (hF : IsMaxTwoMatching (copyEdges E e) F) (hcol : IsTSMColoring F blue)
    (n : ℕ) (hN : Fintype.card (Copy e) = n) :
    unifProb (Copy e) n (fun ω => c * (n : ℝ) ≤ (realOPT E (fun t => (ω t).1) : ℝ) ∧
        ((tsmRun blue (F \ blue) ω).card : ℝ) < (alpha - ε) * (realOPT E (fun t => (ω t).1) : ℝ))
      ≤ 2 * Real.exp ((ε * c) ^ 2 / 32 * N0) * Real.exp (-((ε * c) ^ 2 / 32 * n)) := by
  have hεc : 0 < ε * c := mul_pos hε hc
  have hδ0 : 0 ≤ (ε * c) ^ 2 / 32 := by positivity
  have hE1 : 1 ≤ Real.exp ((ε * c) ^ 2 / 32 * N0) := Real.one_le_exp (by positivity)
  have hexpn : 0 < Real.exp (-((ε * c) ^ 2 / 32 * n)) := Real.exp_pos _
  rcases lt_or_ge n N0 with hlt | hge
  · have h1 := unifProb_le_one' n (fun ω : Fin n → Copy e =>
        c * (n : ℝ) ≤ (realOPT E (fun t => (ω t).1) : ℝ) ∧
        ((tsmRun blue (F \ blue) ω).card : ℝ) < (alpha - ε) * (realOPT E (fun t => (ω t).1) : ℝ))
    have h2 : 1 ≤ Real.exp ((ε * c) ^ 2 / 32 * N0) * Real.exp (-((ε * c) ^ 2 / 32 * n)) := by
      rw [← Real.exp_add]; apply Real.one_le_exp
      have : (n:ℝ) ≤ N0 := by exact_mod_cast hlt.le
      have := mul_le_mul_of_nonneg_left this hδ0
      linarith
    have : 0 < Real.exp ((ε * c) ^ 2 / 32 * N0) * Real.exp (-((ε * c) ^ 2 / 32 * n)) :=
      by positivity
    linarith
  · have hK0 : 0 < 1 + 4 * Real.exp 2 := by positivity
    have hN0pos : (0:ℝ) < N0 := lt_of_le_of_lt (by positivity) hN0
    have hnR : (0:ℝ) < n := lt_of_lt_of_le hN0pos (by exact_mod_cast hge)
    have hn : 0 < n := by exact_mod_cast hnR
    have hne : Nonempty (Copy e) := Fintype.card_pos_iff.mp (hN ▸ hn)
    have hbig : 4 * (1 + 4 * Real.exp 2) < ε * c * n := by
      have h1 : 4 * (1 + 4 * Real.exp 2) / (ε * c) < n :=
        lt_of_lt_of_le hN0 (by exact_mod_cast hge)
      rw [div_lt_iff₀ hεc] at h1; linarith
    have hav := avg_bound E e F blue hF hcol n hN hn
    have hal0 := alpha_pos
    have hal1 := n_alpha_le_one
    have hs0 : 0 ≤ ε * c * n / 4 := by positivity
    have hsub : unifProb (Copy e) n (fun ω => c * (n : ℝ) ≤ (realOPT E (fun t => (ω t).1) : ℝ) ∧
        ((tsmRun blue (F \ blue) ω).card : ℝ) < (alpha - ε) * (realOPT E (fun t => (ω t).1) : ℝ))
        ≤ unifProb (Copy e) n (fun ω =>
          ((tsmRun blue (F \ blue) ω).card : ℝ) ≤
              avg n (fun ω : Fin n → Copy e => ((tsmRun blue (F \ blue) ω).card : ℝ))
                - ε * c * n / 4 ∨
          avg n (fun ω : Fin n → Copy e => (realOPT E (fun t => (ω t).1) : ℝ)) + ε * c * n / 4
            ≤ (realOPT E (fun t => (ω t).1) : ℝ)) := by
      apply unifProb_mono'
      intro ω ⟨h1, h2⟩
      by_contra hcon
      push_neg at hcon
      obtain ⟨h3, h4⟩ := hcon
      set aA := avg n (fun ω : Fin n → Copy e => ((tsmRun blue (F \ blue) ω).card : ℝ))
      set aO := avg n (fun ω : Fin n → Copy e => (realOPT E (fun t => (ω t).1) : ℝ))
      set O := (realOPT E (fun t => (ω t).1) : ℝ)
      set G := ((tsmRun blue (F \ blue) ω).card : ℝ)
      set s := ε * c * n / 4 with hs
      have h5 : alpha * (O - s) < alpha * aO := mul_lt_mul_of_pos_left (by linarith) hal0
      have k1 : ε * (c * n) ≤ ε * O := mul_le_mul_of_nonneg_left h1 hε.le
      have k2 : alpha * s ≤ s := by
        have := mul_le_mul_of_nonneg_right hal1 hs0
        linarith
      have k3 : (alpha - ε) * O = alpha * O - ε * O := by ring
      have k4 : alpha * (O - s) = alpha * O - alpha * s := by ring
      have k5 : ε * (c * n) = 4 * s := by rw [hs]; ring
      linarith
    have hA := mcdiarmid_lower n hn
      (fun ω : Fin n → Copy e => ((tsmRun blue (F \ blue) ω).card : ℝ)) 2 (by norm_num)
      (BD_tsmRun blue (F \ blue) n) _ hs0
    have hO := mcdiarmid_upper n hn
      (fun ω : Fin n → Copy e => (realOPT E (fun t => (ω t).1) : ℝ)) 1 (by norm_num)
      (BD_realOPT E e n) _ hs0
    have heA : Real.exp (-(2 * (ε * c * n / 4) ^ 2 / (n * 2 ^ 2))) =
        Real.exp (-((ε * c) ^ 2 / 32 * n)) := by
      congr 1; field_simp; ring
    have heO : Real.exp (-(2 * (ε * c * n / 4) ^ 2 / (n * 1 ^ 2))) ≤
        Real.exp (-((ε * c) ^ 2 / 32 * n)) := by
      apply Real.exp_le_exp.mpr
      have : 2 * (ε * c * n / 4) ^ 2 / (n * 1 ^ 2) = 4 * ((ε * c) ^ 2 / 32 * n) := by
        field_simp; ring
      rw [this]; linarith [mul_nonneg hδ0 hnR.le]
    have hor := unifProb_or n
      (fun ω : Fin n → Copy e => ((tsmRun blue (F \ blue) ω).card : ℝ) ≤
              avg n (fun ω : Fin n → Copy e => ((tsmRun blue (F \ blue) ω).card : ℝ))
                - ε * c * n / 4)
      (fun ω : Fin n → Copy e =>
          avg n (fun ω : Fin n → Copy e => (realOPT E (fun t => (ω t).1) : ℝ)) + ε * c * n / 4
            ≤ (realOPT E (fun t => (ω t).1) : ℝ))
    have hsum : unifProb (Copy e) n (fun ω => c * (n : ℝ) ≤ (realOPT E (fun t => (ω t).1) : ℝ) ∧
        ((tsmRun blue (F \ blue) ω).card : ℝ) < (alpha - ε) * (realOPT E (fun t => (ω t).1) : ℝ))
        ≤ Real.exp (-((ε * c) ^ 2 / 32 * n)) + Real.exp (-((ε * c) ^ 2 / 32 * n)) := by
      rw [heA] at hA
      linarith [hsub, hor, hA, hO, heO]
    have := mul_le_mul_of_nonneg_right hE1 hexpn.le
    linarith

theorem clause2 : ∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c → ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (A I : Type) [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
        (E : Finset (A × I)) (e : I → ℕ) (F blue : Finset (A × Copy e)),
        IsMaxTwoMatching (copyEdges E e) F → IsTSMColoring F blue →
        unifProb (Copy e) (∑ i, e i) (fun ω =>
            c * ((∑ i, e i : ℕ) : ℝ) ≤ (realOPT E (fun t => (ω t).1) : ℝ) ∧
              ((tsmRun blue (F \ blue) ω).card : ℝ) <
                (alpha - ε) * (realOPT E (fun t => (ω t).1) : ℝ))
          ≤ C * Real.exp (-(δ * ((∑ i, e i : ℕ) : ℝ))) := by
  intro ε hε c hc
  obtain ⟨N0, hN0⟩ := exists_nat_gt (4 * (1 + 4 * Real.exp 2) / (ε * c))
  have hεc : 0 < ε * c := mul_pos hε hc
  refine ⟨2 * Real.exp ((ε * c) ^ 2 / 32 * N0), (ε * c) ^ 2 / 32, by positivity,
    by positivity, ?_⟩
  intro A I _ _ _ _ E e F blue hF hcol
  have hN : Fintype.card (Copy e) = ∑ i, e i := by simp [Copy]
  exact c7_core ε c hε hc N0 hN0 E e F blue hF hcol (∑ i, e i) hN

end C7

open FMMM.TSM in
theorem solution :
    1 - 1 / Real.exp 1 < alpha ∧
    (∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c → ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (A I : Type) [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
        (E : Finset (A × I)) (e : I → ℕ) (F blue : Finset (A × Copy e)),
        IsMaxTwoMatching (copyEdges E e) F → IsTSMColoring F blue →
        unifProb (Copy e) (∑ i, e i) (fun ω =>
            c * ((∑ i, e i : ℕ) : ℝ) ≤ (realOPT E (fun t => (ω t).1) : ℝ) ∧
              ((tsmRun blue (F \ blue) ω).card : ℝ) <
                (alpha - ε) * (realOPT E (fun t => (ω t).1) : ℝ))
          ≤ C * Real.exp (-(δ * ((∑ i, e i : ℕ) : ℝ)))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      IsMaxTwoMatching (tightE m) (tightFlow m) ∧
        ∀ blue : Finset ((Fin 4 × Fin m) × (Fin 4 × Fin m)),
          IsTSMColoring (tightFlow m) blue → expRatio (tightE m) (tightFlow m) blue ≤ alpha + ε) := by
  exact ⟨FMMMProof.clause1, clause2, FMMMProof.clause3⟩

