-- Prove2me | solution 1 for DirectedHamiltonicity.Main.isolated_weighted_trial
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-27T01:51:28.940097+00:00
-- url     : https://prove2.me/submissions/53b5dbdd-e0df-4282-9dff-b594e0c6c26b

import Definitions.Def_DirectedHamiltonicity_Main_ArcCopies
import Theorems.Thm_MulmuleyVV_Matching_lemma1_isolating
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Logic.Equiv.Fin.Basic
import Theorems.Thm_DirectedHamiltonicity_Main_proposition3
import Definitions.Def_DirectedHamiltonicity_Main_DetSum
import Definitions.Def_DirectedHamiltonicity_IsolationTrial

namespace DirectedHamiltonicity.Main.GroupIsolation

open Multidigraph MulmuleyVV.Matching Classical
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}
variable (adj : V → V → Prop) [DecidableRel adj] (S : SArc adj → Finset (Fin d)) (s t : V)
variable (hs : ∀ u, ¬ adj u s)

abbrev Other (s : V) := {v : V // v ≠ s}

def dest (a : ArcCopy adj S) : Other s :=
  ⟨a.1.1.2, fun h => hs a.1.1.1 (h ▸ a.1.2)⟩

def weight (w : Other s × Fin d → ℕ) (a : ArcCopy adj S) : ℕ :=
  w (dest adj S s hs a, a.2.1)

def Uses (sel : Other s → Fin d) (P : Fin (Fintype.card V - 1) → ArcCopy adj S) : Prop :=
  ∀ i, sel (dest adj S s hs (P i)) = (P i).2.1

def support (sel : Other s → Fin d) : Finset (Other s × Fin d) :=
  Finset.univ.image fun v => (v, sel v)

theorem support_injective : Function.Injective (support (d := d) s) := by
  intro a b eq
  funext v
  have h : (v, a v) ∈ support s b := eq ▸ Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
  obtain ⟨u, _, id⟩ := Finset.mem_image.mp h
  obtain rfl : u = v := congrArg Prod.fst id
  exact (congrArg Prod.snd id).symm

private noncomputable def headEquiv (P : Fin (Fintype.card V - 1) → ArcCopy adj S)
    (h : P ∈ (copyGraph adj S).hamPaths s t) : Fin (Fintype.card V - 1) ≃ Other s := by
  apply Equiv.ofBijective (fun i => dest adj S s hs (P i))
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro i j eq
    apply Fin.succ_injective
    apply (Finset.mem_filter.mp h).2.2.1
    exact congrArg Subtype.val eq
  · simp [Other,Fintype.card_subtype_compl]

private theorem existsUnique_uses (P : Fin (Fintype.card V - 1) → ArcCopy adj S)
    (h : P ∈ (copyGraph adj S).hamPaths s t) : ∃! sel, Uses adj S s hs sel P := by
  let e := headEquiv adj S s t hs P h
  change ∃! sel : Other s → Fin d, ∀ i, sel (e i) = (P i).2.val
  refine ⟨fun v => (P (e.symm v)).2.val, fun i => congrArg (fun j => (P j).2.val) (e.symm_apply_apply i), ?_⟩
  intro a ha
  funext v
  simpa using ha (e.symm v)

private theorem pathWeight_of_uses (w : Other s × Fin d → ℕ) (sel : Other s → Fin d)
    (P : Fin (Fintype.card V - 1) → ArcCopy adj S) (h : P ∈ (copyGraph adj S).hamPaths s t)
    (use : Uses adj S s hs sel P) :
    pathWeight (weight adj S s hs w) P = setWeight w (support s sel) := by
  let e := headEquiv adj S s t hs P h
  rw [setWeight,support,Finset.sum_image (fun x _ y _ h => congrArg Prod.fst h)]
  unfold pathWeight
  apply Fintype.sum_equiv e
  intro i
  change w (dest adj S s hs (P i), (P i).2.val) = w (dest adj S s hs (P i), sel _)
  exact congrArg (fun l => w (dest adj S s hs (P i), l)) (use i).symm

private theorem selected_card (sel : Other s → Fin d) :
    ((selectedGraph adj S s sel).hamPaths s t).card =
      (((copyGraph adj S).hamPaths s t).filter (Uses adj S s hs sel)).card := by
  classical
  let proj (P : Fin (Fintype.card V - 1) → {c // InSelectedGroup adj S s sel c}) :=
    fun i => (P i).val
  have lift_iff (P) : P ∈ (selectedGraph adj S s sel).hamPaths s t ↔
      proj P ∈ (copyGraph adj S).hamPaths s t := by
    simp only [hamPaths,Finset.mem_filter,Finset.mem_univ,true_and]
    rfl
  apply Finset.card_bij (fun P _ => proj P)
  · intro P h
    refine Finset.mem_filter.mpr ⟨(lift_iff P).1 h, fun i => ?_⟩
    obtain ⟨_, hl⟩ := (P i).property
    exact hl.symm
  · intro P _ Q _ eq
    exact funext fun i => Subtype.ext (congrFun eq i)
  · intro Q h
    obtain ⟨hp, use⟩ := Finset.mem_filter.mp h
    let P (i) : {c // InSelectedGroup adj S s sel c} :=
      ⟨Q i, (dest adj S s hs (Q i)).property, (use i).symm⟩
    exact ⟨P, (lift_iff P).2 hp, rfl⟩

/-- Partition the copied paths by their incoming group at each non-start vertex. -/
theorem count_by_selection (w : Other s × Fin d → ℕ) (B : ℕ) :
    (copyGraph adj S).weightedPathCount (weight adj S s hs w) s t B =
      ∑ sel : Other s → Fin d, if setWeight w (support s sel) = B
        then ((selectedGraph adj S s sel).hamPaths s t).card else 0 := by
  classical
  let paths := (copyGraph adj S).hamPaths s t
  let total := (paths.filter fun P => pathWeight (weight adj S s hs w) P = B).card
  change _ = _
  have expand : (copyGraph adj S).weightedPathCount (weight adj S s hs w) s t B = total := by
    simp [weightedPathCount,total,paths]
  rw [expand]
  change (paths.filter _).card = _
  simp_rw [Finset.card_filter, selected_card adj S s t hs, Finset.card_filter]
  calc
    _ = ∑ P ∈ paths, ∑ sel : Other s → Fin d,
          if Uses adj S s hs sel P ∧ setWeight w (support s sel) = B then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro P hP
      obtain ⟨sel, hsel, unique⟩ := existsUnique_uses adj S s t hs P hP
      rw [Finset.sum_eq_single sel, pathWeight_of_uses adj S s t hs w sel P hP hsel]
      · simp [hsel]
      · intro b _ hb
        have h : ¬ Uses adj S s hs b P := fun u => hb (unique b u)
        simp [h]
      · simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro sel _
      by_cases h : setWeight w (support s sel) = B <;> simp [h,paths]

noncomputable def oddFamily : Finset (Finset (Other s × Fin d)) :=
  (Finset.univ.filter fun sel : Other s → Fin d => Odd ((selectedGraph adj S s sel).hamPaths s t).card).image (support s)

/-- A unique lightest odd group selection forces an odd coefficient in the weighted path count. -/
theorem odd_weight_of_isolated (w : Other s × Fin d → ℕ)
    (isolated : HasUniqueMin (oddFamily adj S s t) w) :
    ∃ sel : Other s → Fin d, Odd ((copyGraph adj S).weightedPathCount (weight adj S s hs w) s t
      (setWeight w (support s sel))) := by
  classical
  obtain ⟨set, hset, minimal⟩ := isolated
  obtain ⟨sel, hsel, rfl⟩ := Finset.mem_image.mp hset
  have odd := (Finset.mem_filter.mp hsel).2
  refine ⟨sel, ?_⟩
  rw [count_by_selection adj S s t hs]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ sel)]
  simp only [if_true]
  apply Odd.add_even odd
  apply Finset.even_sum
  intro b hb
  by_cases eq : setWeight w (support s b) = setWeight w (support s sel)
  · rw [if_pos eq, ← Nat.not_odd_iff_even]
    intro ho
    have hmem : support s b ∈ oddFamily adj S s t :=
      Finset.mem_image.mpr ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho⟩,rfl⟩
    have ne : b ≠ sel := (Finset.mem_erase.mp hb).1
    exact (minimal _ hmem (fun e => ne (support_injective s e))).ne eq.symm
  · simp [eq]

/-- At least half of the independent weights isolate an odd path coefficient once the family
of odd selections is nonempty. -/
theorem half_weights (good : ∃ sel : Other s → Fin d, Odd ((selectedGraph adj S s sel).hamPaths s t).card) :
    let N := Fintype.card (Other s × Fin d)
    (2*N)^N ≤ 2 * ((Fintype.piFinset fun _ : Other s × Fin d => Finset.Icc 1 (2*N)).filter
      (fun w => ∃ sel : Other s → Fin d, Odd ((copyGraph adj S).weightedPathCount
        (weight adj S s hs w) s t (setWeight w (support s sel))))).card := by
  classical
  obtain ⟨sel, h⟩ := good
  have ne : (oddFamily adj S s t).Nonempty :=
    ⟨support s sel, Finset.mem_image.mpr ⟨sel,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩⟩
  exact (lemma1_isolating _ ne).trans (Nat.mul_le_mul_left _ (Finset.card_le_card
    (Finset.monotone_filter_right _ (fun w _ hi => odd_weight_of_isolated adj S s t hs w hi))))

end DirectedHamiltonicity.Main.GroupIsolation

/-! Counting estimates for independent samples from finite sets. -/

namespace FiniteSampling

open scoped BigOperators
open Classical

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def mean (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α

noncomputable def probability (p : α → Prop) : ℝ :=
  mean fun x => if p x then 1 else 0

theorem probability_eq (p : α → Prop) :
    probability p = ((Finset.univ.filter p).card : ℝ) / Fintype.card α := by
  simp [probability, mean]

theorem mean_mono {f g : α → ℝ} (h : ∀ x, f x ≤ g x) : mean f ≤ mean g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (by positivity)

theorem mean_const [Nonempty α] (c : ℝ) : mean (fun _ : α => c) = c := by
  have h : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean, h, mul_div_cancel_left₀]

theorem mean_sub (f g : α → ℝ) : mean (fun x => f x - g x) = mean f - mean g := by
  simp [mean, Finset.sum_sub_distrib, sub_div]

theorem mean_mul_left (c : ℝ) (f : α → ℝ) : mean (fun x => c * f x) = c * mean f := by
  simp [mean, ← Finset.mul_sum, mul_div_assoc]

theorem mean_sum (f : β → α → ℝ) :
    mean (fun x => ∑ j, f j x) = ∑ j, mean (f j) := by
  unfold mean
  rw [Finset.sum_comm, Finset.sum_div]

theorem probability_not [Nonempty α] (p : α → Prop) :
    probability (fun x => ¬ p x) = 1 - probability p := by
  unfold probability
  conv_rhs => lhs; rw [← mean_const (α := α) 1]
  rw [← mean_sub]
  apply congrArg mean
  funext x
  by_cases h : p x <;> simp [h]

theorem probability_union (p q : α → Prop) :
    probability (fun x => p x ∨ q x) ≤ probability p + probability q := by
  unfold probability
  unfold mean
  rw [← add_div, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro x _
  by_cases hp : p x <;> by_cases hq : q x <;> simp [hp, hq]

theorem probability_exists (p : β → α → Prop) :
    probability (fun x => ∃ j, p j x) ≤ ∑ j, probability (p j) := by
  unfold probability
  rw [← mean_sum]
  apply mean_mono
  intro x
  split_ifs with h
  · obtain ⟨j, hj⟩ := h
    simpa [hj] using (Finset.single_le_sum (f := fun k => if p k x then (1 : ℝ) else 0)
      (fun k _ => by split <;> norm_num) (Finset.mem_univ j))
  · exact Finset.sum_nonneg fun k _ => by split <;> norm_num

theorem probability_mono {p q : α → Prop} (h : ∀ x, p x → q x) :
    probability p ≤ probability q := by
  apply mean_mono
  intro x
  by_cases hp : p x
  · simp [hp, h x hp]
  · simp [hp]; split <;> norm_num

/-- The probability that all independent coordinates have the same property. -/
theorem probability_all (p : α → Prop) (m : ℕ) :
    probability (fun a : Fin m → α => ∀ j, p (a j)) = probability p ^ m := by
  rw [probability_eq, probability_eq]
  have he : (@Finset.filter (Fin m → α) (fun a => ∀ j, p (a j))
      (fun a => Classical.propDecidable _) Finset.univ) =
      Fintype.piFinset (fun _ : Fin m => Finset.univ.filter p) := by
    ext a
    simp [Fintype.mem_piFinset]
  erw [he]
  rw [Fintype.card_piFinset_const, Fintype.card_pi_const]
  push_cast
  rw [div_pow]

/-- Uniform averaging on a pair of independent coordinates. -/
theorem mean_prod (f : α → β → ℝ) :
    mean (fun z : α × β => f z.1 z.2) = mean (fun x => mean (f x)) := by
  simp only [mean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div, div_div]
  rw [mul_comm (Fintype.card β : ℝ)]

theorem probability_prod (p : α → β → Prop) :
    probability (fun z : α × β => p z.1 z.2) = mean (fun x => probability (p x)) := by
  exact mean_prod (fun x y => @ite ℝ (p x y) (Classical.propDecidable _) 1 0)

theorem mean_prod_swap (f : α → β → ℝ) :
    mean (fun x => mean (f x)) = mean (fun y => mean (fun x => f x y)) := by
  simp only [mean, ← Finset.sum_div, div_div]
  rw [Finset.sum_comm, mul_comm (Fintype.card β : ℝ)]

/-- A counting form of Markov's inequality; no independence is needed. -/
theorem markov (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) {c : ℝ} (hc : 0 < c) :
    probability (fun x => c < f x) ≤ mean f / c := by
  apply (le_div_iff₀ hc).2
  rw [mul_comm, probability, ← mean_mul_left]
  apply mean_mono
  intro x
  by_cases hx : c < f x
  · simpa [hx] using hx.le
  · simpa [hx] using hf x

/-- One block misses with probability at most one half if its expected hit count is at least one. -/
theorem miss_block {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) {k : ℕ} (hk : 1 ≤ k * p) :
    (1 - p) ^ k ≤ 1 / 2 := by
  have hbern : 2 ≤ (1 + p) ^ k := by
    linarith [one_add_mul_le_pow (by linarith : -2 ≤ p) k]
  have hprod : ((1 - p) ^ k) * ((1 + p) ^ k) ≤ 1 := by
    rw [← mul_pow]
    apply pow_le_one₀ (mul_nonneg (by linarith) (by linarith))
    nlinarith [sq_nonneg p]
  nlinarith only [hprod, mul_nonneg (pow_nonneg (sub_nonneg.mpr hp') k) (sub_nonneg.mpr hbern)]

end FiniteSampling

namespace FiniteSampling

open Classical
variable {A B : Type*} [Fintype A] [Fintype B]

theorem probability_equiv (e : A ≃ B) (p : B → Prop) :
    probability (fun a => p (e a)) = probability p := by
  unfold probability mean
  rw [Fintype.card_congr e]
  congr 1
  exact e.sum_comp (fun b => @ite ℝ (p b) (Classical.propDecidable _) 1 0)

/-- Split a tape at a known position. The first component is exactly the prefix of that length. -/
def splitCoins (r s : ℕ) : (Fin (r + s) → Bool) ≃ (Fin r → Bool) × (Fin s → Bool) :=
  (finSumFinEquiv.symm.arrowCongr (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

/-- Assign a mask to each row by reading a fixed number of bits per trial. -/
def trialBlocks (m width : ℕ) : (Fin (m * width) → Bool) ≃ (Fin m → Fin width → Bool) :=
  (finProdFinEquiv.symm.arrowCongr (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

@[simp] theorem splitCoins_fst (r s : ℕ) (c : Fin (r + s) → Bool) (i : Fin r) :
    (splitCoins r s c).1 i = c (Fin.castAdd s i) := rfl

/-- A property of a fixed prefix has the same probability on every longer uniform tape. -/
theorem probability_prefix {r length : ℕ} (h : r ≤ length) (p : (Fin r → Bool) → Prop) :
    probability (fun c : Fin length → Bool => p (fun i => c (Fin.castLE h i))) = probability p := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
  let e := splitCoins r extra
  have he := probability_equiv e (fun z => p z.1)
  have h₁ : probability (fun z : (Fin r → Bool) × (Fin extra → Bool) => p z.1) = probability p := by
    rw [probability_prod (fun x _ => p x)]
    unfold probability
    congr 1
    funext x
    exact mean_const _
  exact he.trans h₁

end FiniteSampling

namespace DirectedHamiltonicity.Main.CycleReduction

open GroupIsolation Multidigraph FiniteSampling Classical
open scoped BigOperators

/-- One equally likely symbol deletes an arc and seven symbols encode each nonempty subset. -/
def copyMask (u : Fin 50) : Finset (Fin 3) :=
  Finset.univ.filter fun j => (if u.val = 0 then 0 else 1 + (u.val-1)/7).testBit j.val

private theorem mask_count : ∀ s : Finset (Fin 3),
    (Finset.univ.filter (fun x : Fin 50 => copyMask x = s)).card = (if s = ∅ then 1 else 7) := by
  decide

private theorem mask_mass (s : Finset (Fin 3)) :
    ((Finset.univ.filter (fun x : Fin 50 => copyMask x = s)).card : ℝ) / 50 = copySetProb 3 s := by
  rw [mask_count,copySetProb]
  split <;> norm_num [delta]

private theorem masks_fiber {A : Type} [Fintype A] (S : A → Finset (Fin 3)) :
    (Finset.univ.filter (fun r : A → Fin 50 => (fun a => copyMask (r a)) = S)).card =
      ∏ a, (Finset.univ.filter (fun x : Fin 50 => copyMask x = S a)).card := by
  classical
  have eq : (Finset.univ.filter (fun r : A → Fin 50 => (fun a => copyMask (r a)) = S)) =
      Fintype.piFinset (fun a => Finset.univ.filter fun x : Fin 50 => copyMask x = S a) := by
    ext r
    simp [Fintype.mem_piFinset,funext_iff]
  rw [eq,Fintype.card_piFinset]

theorem mask_probability {A : Type} [Fintype A] [DecidableEq A]
    (E : (A → Finset (Fin 3)) → Prop) :
    probability (fun r : A → Fin 50 => E (fun a => copyMask (r a))) =
      (∑ S ∈ Finset.univ.filter E, ∏ a, copySetProb 3 (S a)) := by
  classical
  let decode := fun (r : A → Fin 50) a => copyMask (r a)
  let G := Finset.univ.filter E
  let U := Finset.univ.filter (fun r => E (decode r))
  have fibers := Finset.card_eq_sum_card_fiberwise (s := U) (t := G) (f := decode)
    (fun r h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩)
  rw [probability_eq]
  change (U.card : ℝ) / _ = _
  rw [fibers,Nat.cast_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro S good
  have ok := (Finset.mem_filter.mp good).2
  have fiber : U.filter (fun r => decode r = S) = Finset.univ.filter (fun r => decode r = S) := by
    ext r
    simp only [U,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨And.right,fun e => ⟨e ▸ ok,e⟩⟩
  rw [fiber]
  let per := fun a => Finset.univ.filter (fun x : Fin 50 => copyMask x = S a)
  have same : Finset.univ.filter (fun r : A → Fin 50 => decode r = S) =
      Fintype.piFinset per := by
    ext r
    simp [decode,per,funext_iff,Fintype.mem_piFinset]
  rw [same,Fintype.card_piFinset,Nat.cast_prod]
  dsimp only [per]
  simp_rw [← mask_mass]
  rw [Finset.prod_div_distrib]
  simp [Fintype.card_fun]

theorem sample_copy_law {V : Type} [Fintype V] [DecidableEq V] {adj : V → V → Prop} [DecidableRel adj]
    (E : (SArc adj → Finset (Fin 3)) → Prop) :
    probability (fun r : SArc adj → Fin 50 => E (fun a => copyMask (r a))) =
      copyProb (adj := adj) 3 E := by
  classical
  refine (mask_probability E).trans ?_
  unfold copyProb assignProb
  apply Finset.sum_congr (by ext f; simp)
  intro S _
  apply Finset.prod_congr (by ext a; simp)
  intro a _
  rfl

variable {V : Type} [Fintype V] [DecidableEq V] (adj : V → V → Prop) [DecidableRel adj]
variable (s t : V) (hs : ∀ u, ¬ adj u s)

abbrev Labels (s : V) := Other s × Fin 3
abbrev labelCount (s : V) := Fintype.card (Labels s)

def labelWeight (v : Labels s → Fin (2*labelCount s)) (x : Labels s) : ℕ := (v x).val+1

private noncomputable def weightEquiv : (Labels s → Fin (2*labelCount s)) ≃
    {w // w ∈ Fintype.piFinset (fun _ : Labels s => Finset.Icc 1 (2*labelCount s))} where
  toFun u := ⟨labelWeight s u,Fintype.mem_piFinset.mpr (fun x =>
    Finset.mem_Icc.mpr ⟨Nat.succ_pos _,(u x).isLt⟩)⟩
  invFun w x := ⟨w.1 x-1,by
    obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp w.2 x)
    omega⟩
  left_inv u := by funext x; apply Fin.ext; simp [labelWeight]
  right_inv w := by
    apply Subtype.ext
    funext x
    have lo := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp w.2 x)).1
    dsimp [labelWeight];omega

private theorem half_of_count {A : Type} [Fintype A] (p : A → Prop) (outcomes : Finset A)
    (mem_iff : ∀ x, x ∈ outcomes ↔ p x) (pos : 0 < Fintype.card A)
    (h : Fintype.card A ≤ 2*outcomes.card) : (1/2:ℝ) ≤ probability p := by
  rw [probability_eq]
  have eq : (Finset.univ.filter p)=outcomes := by ext x; simp [mem_iff]
  rw [eq]
  apply (le_div_iff₀ (by exact_mod_cast pos : (0:ℝ)<Fintype.card A)).2
  have real : (Fintype.card A:ℝ) ≤ 2*outcomes.card := by exact_mod_cast h
  linarith

private theorem two_stage {A B : Type} [Fintype A] [Fintype B] (g : A → Prop) (test : A → B → Prop)
    (p : ℝ) (conditional : ∀ a, g a → p ≤ probability (test a)) :
    p * probability g ≤ probability (fun z : A × B => test z.1 z.2) := by
  rw [probability_prod test]
  change p * mean (fun a => if g a then 1 else 0) ≤ _
  rw [← mean_mul_left]
  apply mean_mono
  intro a
  by_cases h : g a
  · simpa [h] using conditional a h
  · simp only [if_neg h,mul_zero];rw [probability_eq]; positivity

private theorem weight_probability (S : SArc adj → Finset (Fin 3))
    (good : ∃ sel : Other s → Fin 3, Odd ((selectedGraph adj S s sel).hamPaths s t).card) :
    (1/2 : ℝ) ≤ probability (fun u : Labels s → Fin (2*labelCount s) =>
        ∃ B : ℕ, B ≤ (Fintype.card V-1)*(2*labelCount s) ∧
        Odd ((copyGraph adj S).weightedPathCount (weight adj S s hs (labelWeight s u)) s t B)) := by
  classical
  let box := Fintype.piFinset (fun _ : Labels s => Finset.Icc 1 (2*labelCount s))
  let Q := fun w : Labels s → ℕ => ∃ sel : Other s → Fin 3, Odd ((copyGraph adj S).weightedPathCount
    (weight adj S s hs w) s t (MulmuleyVV.Matching.setWeight w (support s sel)))
  have half : (2*labelCount s)^(labelCount s) ≤ 2 * (box.filter Q).card :=
    half_weights adj S s t hs good
  let e := weightEquiv s
  have count : (Finset.univ.filter (fun u => Q (labelWeight s u))).card = (box.filter Q).card := by
    apply Finset.card_bij (fun u _ => (e u).1)
    · intro u h
      exact Finset.mem_filter.mpr ⟨(e u).2, (Finset.mem_filter.mp h).2⟩
    · intro u _ v _ h; exact e.injective (Subtype.ext h)
    · intro w h
      obtain ⟨hbox,hq⟩ := Finset.mem_filter.mp h
      let z : {w // w ∈ box} := ⟨w,hbox⟩
      have eq := congrArg Subtype.val (e.apply_symm_apply z)
      have eq' : labelWeight s (e.symm z) = w := eq
      exact ⟨e.symm z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq'.symm ▸ hq⟩,eq⟩
  have term : (1/2 : ℝ) ≤ probability (fun u => Q (labelWeight s u)) := by
    have card : Fintype.card (Labels s → Fin (2*labelCount s)) = (2*labelCount s)^(labelCount s) := by
      simp only [Fintype.card_fun,Fintype.card_fin]
    apply half_of_count _ (Finset.univ.filter (fun u => Q (labelWeight s u)))
    · intro u; simp
    · rw [card]
      cases h : labelCount s with
      | zero => simp
      | succ k => positivity
    · exact card.trans_le (half.trans_eq (congrArg (2*·) count.symm))
  apply term.trans (probability_mono ?_)
  rintro u ⟨sel,odd⟩
  refine ⟨_,?_,odd⟩
  rw [MulmuleyVV.Matching.setWeight,support,Finset.sum_image (fun i _ j _ eq => congrArg Prod.fst eq)]
  calc
    _ ≤ ∑ _ : Other s, 2*labelCount s := Finset.sum_le_sum fun i _ => (u (i,sel i)).isLt
    _ = _ := by simp [Other,Fintype.card_subtype_compl]

/-- One fully finite trial has an odd target coefficient with probability at least
one half times the survival probability of Proposition 3. -/
theorem isolated_trial (hne : s ≠ t) (hloop : ∀ v, ¬ adj v v) (ht : ∀ v, ¬ adj t v)
    (hpath : ((ofAdj adj).hamPaths s t).Nonempty) :
    (1/2 : ℝ)*(49/50 : ℝ)^(Fintype.card V-1) ≤
    probability (fun z : (SArc adj → Fin 50) × (Labels s → Fin (2*labelCount s)) =>
      let S := fun a => copyMask (z.1 a)
      ∃ B : ℕ, B ≤ (Fintype.card V-1)*(2*labelCount s) ∧
        Odd ((copyGraph adj S).weightedPathCount (weight adj S s hs (labelWeight s z.2)) s t B)) := by
  classical
  let good := fun (S : SArc adj → Finset (Fin 3)) =>
    ∃ sel : Other s → Fin 3, Odd ((selectedGraph adj S s sel).hamPaths s t).card
  have h := proposition3 adj s t hne hloop hs ht 3 (by decide) hpath
  change (1-delta 3)^(Fintype.card V-1) ≤ copyProb 3 good at h
  have distribution := sample_copy_law (adj := adj) good
  rw [← distribution,show 1-delta 3 = (49/50 : ℝ) by norm_num [delta]] at h
  refine (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 1/2)).trans ?_
  let target := fun (r : SArc adj → Fin 50) (u : Labels s → Fin (2*labelCount s)) =>
    let S := fun a => copyMask (r a)
    ∃ B : ℕ, B ≤ (Fintype.card V-1)*(2*labelCount s) ∧
      Odd ((copyGraph adj S).weightedPathCount (weight adj S s hs (labelWeight s u)) s t B)
  change _ ≤ probability (fun z : _ × _ => target z.1 z.2)
  apply two_stage (fun r : SArc adj → Fin 50 => good (fun a => copyMask (r a))) target (1/2)
  intro r hit
  exact weight_probability adj s t hs (fun a => copyMask (r a)) hit

end DirectedHamiltonicity.Main.CycleReduction

open DirectedHamiltonicity.Main

open Classical in
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) [DecidableRel adj] (s t : V) (hst : s ≠ t)
    (hloop : ∀ v, ¬ adj v v) (hs : ∀ u, ¬ adj u s) (ht : ∀ v, ¬ adj t v)
    (hp : ((ofAdj adj).hamPaths s t).Nonempty) :
    (1/2 : ℝ) * (49/50 : ℝ)^(Fintype.card V-1) ≤
      ((Finset.univ.filter (IsolationTrial.Hits adj s t hs)).card : ℝ) /
        Fintype.card (IsolationTrial.Seed adj s) := by
  have trial := CycleReduction.isolated_trial adj s t hs hst hloop ht hp
  change _ ≤ FiniteSampling.probability (IsolationTrial.Hits adj s t hs) at trial
  rw [FiniteSampling.probability_eq] at trial
  exact trial
