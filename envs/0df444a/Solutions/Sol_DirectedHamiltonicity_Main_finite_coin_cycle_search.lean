-- Prove2me | solution 1 for DirectedHamiltonicity.Main.finite_coin_cycle_search
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:10:01.549873+00:00
-- url     : https://prove2.me/submissions/85c63640-f9fd-47d0-ba51-08f5ac390ba0

import Mathlib
import Definitions.Def_DirectedHamiltonicity_CycleSearch
import Theorems.Thm_DirectedHamiltonicity_Main_isolated_weighted_trial
import Theorems.Thm_DirectedHamiltonicity_Main_cycle_iff_closing_path
import Theorems.Thm_DirectedHamiltonicity_Main_proposition4

section

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

theorem markov (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) {c : ℝ} (hc : 0 < c) :
    probability (fun x => c < f x) ≤ mean f / c := by
  apply (le_div_iff₀ hc).2
  rw [mul_comm, probability, ← mean_mul_left]
  apply mean_mono
  intro x
  by_cases hx : c < f x
  · simpa [hx] using hx.le
  · simpa [hx] using hf x

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

end

section

namespace FiniteSampling

open Classical

variable {A U X : Type*}

@[simp] theorem padded_code (code : A ↪ U) (family : A → Finset X) (a : A) :
    padded code family (code a) = family a := by
  have h : ∃ v, code v = code a := ⟨a, rfl⟩
  simp only [padded, dif_pos h, code.injective h.choose_spec]

theorem padded_empty (code : A ↪ U) (family : A → Finset X) {u : U}
    (h : ¬∃ a, code a = u) : padded code family u = ∅ := by simp [padded, h]

variable [Fintype A] [Fintype U]

private theorem padded_hits (code : A ↪ U) (family : A → Finset X) (x : X) :
    (@Finset.filter U (fun u => x ∈ padded code family u) (fun _ => Classical.propDecidable _) Finset.univ).card =
      (@Finset.filter A (fun a => x ∈ family a) (fun _ => Classical.propDecidable _) Finset.univ).card := by
  calc
    _ = ((@Finset.filter A (fun a => x ∈ family a) (fun _ => Classical.propDecidable _) Finset.univ).map code).card := by
      congr 1
      ext u
      by_cases h : ∃ a, code a = u
      · obtain ⟨a, rfl⟩ := h
        simp
      · simp [padded_empty _ _ h, Finset.mem_map]
        exact fun a _ => fun ha => h ⟨a, ha⟩
    _ = _ := Finset.card_map _

theorem padded_hit_lower [Nonempty A] [Nonempty U] (code : A ↪ U) (family : A → Finset X)
    (hwidth : Fintype.card U ≤ 2 * Fintype.card A) (x : X) :
    probability (fun a => x ∈ family a) ≤ 2 * probability (fun u => x ∈ padded code family u) := by
  simp only [probability_eq]
  rw [padded_hits, ← mul_div_assoc]
  apply (div_le_div_iff₀ (by exact_mod_cast Fintype.card_pos (α := A))
    (by exact_mod_cast Fintype.card_pos (α := U))).2
  have hw : (Fintype.card U : ℝ) ≤ 2 * Fintype.card A := by exact_mod_cast hwidth
  have h := mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg (α := ℝ)
    (@Finset.filter A (fun a => x ∈ family a) (fun _ => Classical.propDecidable _) Finset.univ).card)
  linarith only [h]

theorem coinBlock_bounds (A : Type*) [Fintype A] [Nonempty A] :
    Fintype.card A ≤ Fintype.card (CoinBlock A) ∧
      Fintype.card (CoinBlock A) ≤ 2 * Fintype.card A := by
  simp only [CoinBlock, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  let N := Fintype.card A
  change N ≤ 2 ^ Nat.clog 2 N ∧ 2 ^ Nat.clog 2 N ≤ 2 * N
  refine ⟨Nat.le_pow_clog (by decide) _, ?_⟩
  have hn : 0 < N := Fintype.card_pos
  by_cases h : 1 < N
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.clog_pos (by decide : 1 < 2) h).ne'
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) h
    rw [hj] at hp ⊢
    simp only [Nat.pred_succ] at hp
    rw [pow_succ]
    omega
  · have he : N = 1 := by omega
    simp [he]

end FiniteSampling

end

section

namespace FiniteSampling

open scoped BigOperators

theorem tupleRank_digit {I : Type*} {k : ℕ} {A : I → Type*} (order : I ≃ Fin k)
    (radix : I → ℕ) (row : ∀ i, A i ≃ Fin (radix i))
    (z : Fin (∏ j : Fin k, radix (order.symm j))) (j : Fin k) :
    (row (order.symm j) ((tupleRank order radix row).symm z (order.symm j))).val =
      (z.val / (∏ h : Fin j.val, radix (order.symm (Fin.castLE j.isLt.le h)))) % radix (order.symm j) := by
  let a := (tupleRank order radix row).symm z
  let digit := fun i : Fin k => row (order.symm i) (a (order.symm i))
  have hz : finPiFinEquiv digit = z := (tupleRank order radix row).apply_symm_apply z
  have hd := congrArg (fun x => (finPiFinEquiv (n := fun i => radix (order.symm i))).symm x j) hz
  simp only [Equiv.symm_apply_apply] at hd
  exact congrArg Fin.val hd

theorem nonzeroRowRank_bit {I : Type*} {k : ℕ} (cols : I ≃ Fin k) (z : Fin (2^k-1)) (i : I) :
    (((nonzeroRowRank cols).symm z).val i).val = ((z.val+1)/2^(cols i).val)%2 := rfl

variable {A : Type*} [Fintype A] {N : ℕ}

def rankedCode (rank : A ≃ Fin N) : A ↪ CoinBlock A :=
  let width := Nat.clog 2 (Fintype.card A)
  let h : N ≤ 2^width := by
    have hc := Fintype.card_congr rank
    rw [Fintype.card_fin] at hc
    exact hc ▸ Nat.le_pow_clog (by decide) (Fintype.card A)
  { toFun := fun x => (binaryRank width).symm (Fin.castLE h (rank x))
    inj' := by
      intro x y hxy
      apply rank.injective
      apply Fin.ext
      exact congrArg (fun u : Fin (2^width) => u.val) ((binaryRank width).symm.injective hxy) }

@[simp] theorem rankedCode_value (rank : A ≃ Fin N) (x : A) :
    (binaryRank _ (rankedCode rank x)).val = (rank x).val := by
  change ((binaryRank _) ((binaryRank _).symm _)).val = _
  simp

@[simp] theorem decodeRank_code (rank : A ≃ Fin N) (x : A) :
    decodeRank rank (rankedCode rank x) = some x := by
  simp [decodeRank, (rank x).isLt]

theorem rankedCode_of_decode {rank : A ≃ Fin N} {bits : CoinBlock A} {x : A}
    (h : decodeRank rank bits = some x) : rankedCode rank x = bits := by
  dsimp only [decodeRank] at h
  split at h
  · cases Option.some.inj h
    apply (binaryRank _).injective
    apply Fin.ext
    simp
  · contradiction

theorem padded_eq_decode {X : Type*} (rank : A ≃ Fin N) (family : A → Finset X) (bits : CoinBlock A) :
    padded (rankedCode rank) family bits = (decodeRank rank bits).elim ∅ family := by
  cases he : decodeRank rank bits with
  | none =>
    rw [padded_empty]
    · rfl
    rintro ⟨x, rfl⟩
    simp at he
  | some x =>
    have h := rankedCode_of_decode he
    rw [← h, padded_code]
    rfl

end FiniteSampling

end

section

namespace FiniteSampling

open Classical

variable {A B : Type*} [Fintype A] [Fintype B]

theorem probability_equiv (e : A ≃ B) (p : B → Prop) :
    probability (fun a => p (e a)) = probability p := by
  unfold probability mean
  rw [Fintype.card_congr e]
  congr 1
  exact e.sum_comp (fun b => @ite ℝ (p b) (Classical.propDecidable _) 1 0)

@[simp] theorem splitCoins_fst (r s : ℕ) (c : Fin (r + s) → Bool) (i : Fin r) :
    (splitCoins r s c).1 i = c (Fin.castAdd s i) := rfl

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

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open GroupIsolation Multidigraph FiniteSampling Classical

open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V] (adj : V → V → Prop) [DecidableRel adj]

variable (s t : V) (hs : ∀ u, ¬ adj u s)

theorem isolated_trial (hne : s ≠ t) (hloop : ∀ v, ¬ adj v v) (ht : ∀ v, ¬ adj t v)
    (hpath : ((ofAdj adj).hamPaths s t).Nonempty) :
    (1/2 : ℝ)*(49/50 : ℝ)^(Fintype.card V-1) ≤
    probability (fun z : (SArc adj → Fin 50) × (Labels s → Fin (2*labelCount s)) =>
      let S := fun a => copyMask (z.1 a)
      ∃ B : ℕ, B ≤ (Fintype.card V-1)*(2*labelCount s) ∧
        Odd ((copyGraph adj S).weightedPathCount (weight adj S s hs (labelWeight s z.2)) s t B)) := by
  have h := DirectedHamiltonicity.Main.isolated_weighted_trial adj s t hne hloop hs ht hpath
  change _ ≤ probability (IsolationTrial.Hits adj s t hs)
  rw [probability_eq]
  exact h

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open Multidigraph Classical

theorem cycle_iff_closing_path {n : ℕ} (hn : 2 ≤ n) (adj : Fin n → Fin n → Bool) :
    HasHamCycle n adj ↔ ∃ s t : Fin n, s ≠ t ∧ adj t s = true ∧
      ((ofAdj (pathAdj adj s t)).hamPaths s t).Nonempty := by
  exact DirectedHamiltonicity.Main.cycle_iff_closing_path hn adj

theorem smallCycleAnswer_correct {n : ℕ} (hn : n ≤ 1) (adj : Fin n → Fin n → Bool) :
    smallCycleAnswer n adj = true ↔ HasHamCycle n adj := by
  interval_cases n
  · simp [smallCycleAnswer,HasHamCycle]
  · change adj 0 0 = true ↔ _
    simp only [HasHamCycle, Nat.zero_lt_succ, true_and]
    constructor
    · intro h
      refine ⟨Equiv.refl _, fun i => ?_⟩
      simpa only [Subsingleton.elim i (0 : Fin 1),finRotate_one,Equiv.refl_apply] using h
    · rintro ⟨σ,h⟩
      simpa only [finRotate_one,Equiv.refl_apply,Subsingleton.elim (σ 0) (0 : Fin 1)] using h 0

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open Classical FiniteSampling

open scoped BigOperators

theorem probability_restrict {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
    (p : I → Prop) [DecidablePred p] (event : ({i // p i} → A) → Prop) :
    probability (fun f : I → A => event (fun i => f i.val)) = probability event := by
  classical
  let e := ((Equiv.sumCompl p).symm.arrowCongr (Equiv.refl A)).trans
    (Equiv.sumArrowEquivProdArrow _ _ A)
  have pair := probability_equiv e (fun z => event z.1)
  have first (f : I → A) : (e f).1 = fun i => f i.val := by
    funext i
    rfl
  rw [show (fun f : I → A => event (fun i => f i.val)) = (fun f => event (e f).1) by
    funext f;rw [first],pair,probability_prod (fun a _ => event a)]
  unfold probability
  apply congrArg mean
  funext a
  exact mean_const _

theorem probability_guess {A J : Type} [Fintype A] [Fintype J] [Nonempty J]
    (hit : A → J → Prop) :
    probability (fun a => ∃ j, hit a j) ≤ Fintype.card J * probability (fun z : A × J => hit z.1 z.2) := by
  rw [probability_prod hit,← mean_mul_left]
  apply mean_mono
  intro a
  rw [probability_eq]
  have pos : (0:ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  rw [mul_comm (Fintype.card J:ℝ),div_mul_cancel₀ _ pos.ne']
  by_cases h : ∃ j, hit a j
  · obtain ⟨j,hj⟩ := h
    simp only [if_pos (show ∃ k, hit a k from ⟨j,hj⟩)]
    exact_mod_cast Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  · simp [h]

theorem single_contribution {I A : Type} [Fintype I] [Fintype A] [Nonempty I]
    (event : I → A → Prop) (i : I) :
    probability (event i) ≤ Fintype.card I * probability (fun z : I × A => event z.1 z.2) := by
  rw [probability_prod event,mean,mul_comm (Fintype.card I:ℝ),div_mul_cancel₀ _ (by exact_mod_cast (Fintype.card_ne_zero (α := I)) : (Fintype.card I:ℝ)≠0)]
  exact Finset.single_le_sum (f := fun j => probability (event j))
    (fun j _ => by rw [probability_eq];positivity) (Finset.mem_univ _)

theorem all_miss {A : Type} [Fintype A] [Nonempty A] (hit : A → Prop) (k blocks : ℕ)
    (coverage : (1:ℝ) ≤ k * probability hit) :
    probability (fun x : Fin (k*blocks) → A => ∀ i, ¬hit (x i)) ≤ (1/2:ℝ)^blocks := by
  have pos : 0 ≤ probability hit := by rw [probability_eq];positivity
  have le : probability hit ≤ 1 := by
    have h : 0 ≤ probability (fun x => ¬hit x) := by rw [probability_eq];positivity
    rw [probability_not] at h
    linarith
  rw [probability_all (fun a => ¬hit a),probability_not,pow_mul]
  exact pow_le_pow_left₀ (by positivity) (miss_block pos le coverage) _

theorem padded_event {A : Type} [Fintype A] [Nonempty A] (code : A ↪ CoinBlock A) (hit : A → Prop) :
    probability hit ≤ 2*probability (fun bits : CoinBlock A => ∃ a, code a = bits ∧ hit a) := by
  classical
  let family := fun a : A => if hit a then ({()} : Finset Unit) else ∅
  have lower := padded_hit_lower code family (coinBlock_bounds A).2 ()
  have left : (fun a => () ∈ family a) = hit := by funext a;by_cases h : hit a <;> simp [family,h]
  rw [left] at lower
  refine lower.trans (mul_le_mul_of_nonneg_left (probability_mono ?_) (by norm_num))
  intro bits hb
  by_cases has : ∃ a, code a = bits
  · obtain ⟨a,rfl⟩ := has
    refine ⟨a,rfl,?_⟩
    by_contra no
    simpa [family,no] using hb
  · rw [padded_empty _ _ has] at hb
    contradiction

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

section Search

variable {E : Type} [DecidableEq E]

theorem prune_subset (ask : E → Finset E → Bool) (G : Finset E) (es : List E) :
    prune ask G es ⊆ G := by
  induction es generalizing G with
  | nil => rfl
  | cons e es ih =>
    exact (ih _).trans (by split <;> first | exact Finset.erase_subset .. | exact Finset.Subset.refl _)

def feasible (F : Finset (Finset E)) (G : Finset E) : Prop := ∃ W ∈ F, W ⊆ G

theorem feasible_mono (F : Finset (Finset E)) {A B : Finset E} (h : A ⊆ B) :
    feasible F A → feasible F B := fun ⟨W,hW,sub⟩ => ⟨W,hW,sub.trans h⟩

open Classical in
noncomputable def exactAnswer (F : Finset (Finset E)) (_ : E) (G : Finset E) : Bool :=
  decide (feasible F G)

open Classical in
private theorem prune_invariant (F : Finset (Finset E)) (G : Finset E) (es : List E)
    (possible : feasible F G) :
    let R := prune (exactAnswer F) G es
    feasible F R ∧ ∀ e ∈ es, e ∈ R → ¬ feasible F (R.erase e) := by
  induction es generalizing G with
  | nil => exact ⟨possible,by simp⟩
  | cons e es ih =>
    dsimp only [prune]
    by_cases h : feasible F (G.erase e)
    · simp only [exactAnswer,decide_eq_true_eq,if_pos h]
      obtain ⟨ok,minimal⟩ := ih _ h
      refine ⟨ok, fun a ha haR => ?_⟩
      rcases List.mem_cons.mp ha with rfl | inTail
      · exact False.elim (Finset.notMem_erase _ _ ((prune_subset _ _ _ ) haR))
      · exact minimal a inTail haR
    · simp only [exactAnswer,decide_eq_true_eq,if_neg h]
      obtain ⟨ok,minimal⟩ := ih _ possible
      refine ⟨ok, fun a ha haR => ?_⟩
      rcases List.mem_cons.mp ha with rfl | inTail
      · exact fun bad => h (feasible_mono F (Finset.erase_subset_erase _ (prune_subset ..)) bad)
      · exact minimal a inTail haR

theorem prune_recovers (F : Finset (Finset E)) (G : Finset E) (es : List E)
    (cover : ∀ e ∈ G, e ∈ es) (possible : feasible F G) :
    prune (exactAnswer F) G es ∈ F := by
  let R := prune (exactAnswer F) G es
  obtain ⟨⟨W, hw, sub⟩,minimal⟩ := prune_invariant F G es possible
  have rev : R ⊆ W := by
    intro e he
    by_contra miss
    have hit : e ∈ es := cover _ (prune_subset _ G es he)
    exact minimal e hit he ⟨W,hw,(Finset.subset_erase.mpr ⟨sub,miss⟩)⟩
  change R ∈ F
  rw [Finset.Subset.antisymm rev sub]
  exact hw

def queries (ask : E → Finset E → Bool) (G : Finset E) : List E → List (E × Finset E)
  | [] => []
  | e :: es => (e,G.erase e) :: queries ask (if ask e (G.erase e) then G.erase e else G) es

@[simp] theorem queries_length (ask : E → Finset E → Bool) (G : Finset E) (es : List E) :
    (queries ask G es).length = es.length := by
  induction es generalizing G with
  | nil => rfl
  | cons e es ih => simp [queries,ih]

theorem prune_of_correct_transcript (ref ask : E → Finset E → Bool) (G : Finset E) (es : List E)
    (agree : ∀ q ∈ queries ref G es, ask q.1 q.2 = ref q.1 q.2) :
    prune ask G es = prune ref G es := by
  induction es generalizing G with
  | nil => rfl
  | cons e es ih =>
    have fst := agree (e,G.erase e) (List.mem_cons_self ..)
    simp only [prune, fst]
    apply ih
    intro q h
    exact agree q (List.mem_cons_of_mem _ h)

end Search

open Classical in
def cycleEdges {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.image fun i => (σ i,σ (finRotate n i))

open Classical in
noncomputable def cycles (n : ℕ) : Finset (Finset (Fin n × Fin n)) :=
  if 0 < n then Finset.univ.image cycleEdges else ∅

theorem graph_feasible {n : ℕ} (adj : Fin n → Fin n → Bool) :
    feasible (cycles n) (edges adj) ↔ HasHamCycle n adj := by
  classical
  by_cases hn : 0 < n
  · simp only [cycles,if_pos hn,HasHamCycle,hn,true_and]
    constructor
    · rintro ⟨W,hW,sub⟩
      obtain ⟨σ,_,rfl⟩ := Finset.mem_image.mp hW
      exact ⟨σ,fun i => (Finset.mem_filter.mp (sub (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))).2⟩
    · rintro ⟨σ,hσ⟩
      refine ⟨cycleEdges σ,Finset.mem_image.mpr ⟨σ,Finset.mem_univ _,rfl⟩,?_⟩
      intro p hp
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hσ i⟩
  · simp [feasible,cycles,hn,HasHamCycle]

theorem verified_prune_sound {n : ℕ} (adj : Fin n → Fin n → Bool) (es : List (Fin n × Fin n))
    (ask : Fin n × Fin n → Finset (Fin n × Fin n) → Bool)
    (verify : prune ask (edges adj) es ∈ cycles n) : HasHamCycle n adj :=
  (graph_feasible adj).mp ⟨_,verify,prune_subset ..⟩

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open FiniteSampling Classical

open scoped BigOperators

private theorem list_union {Ω Q : Type*} [Fintype Ω] (qs : List Q) (bad : Q → Ω → Prop) (ε : ℝ)
    (h : ∀ q ∈ qs, probability (bad q) ≤ ε) :
    probability (fun ω => ∃ q ∈ qs, bad q ω) ≤ qs.length * ε := by
  induction qs with
  | nil => simp [probability_eq]
  | cons a qs ih =>
    simp only [List.mem_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    have eq (ω : Ω) : (∃ q, (q = a ∨ q ∈ qs) ∧ bad q ω) ↔
        bad a ω ∨ ∃ q ∈ qs, bad q ω := by aesop
    try simp only [eq]
    have one := h a (List.mem_cons_self ..)
    have rest := ih (fun q hq => h _ (List.mem_cons_of_mem _ hq))
    have union := probability_union (bad a) (fun ω => ∃ q ∈ qs, bad q ω)
    linarith

theorem prune_probability {E Ω : Type} [DecidableEq E] [Fintype Ω] [Nonempty Ω]
    (F : Finset (Finset E)) (G : Finset E) (es : List E) (cover : ∀ e ∈ G, e ∈ es)
    (possible : feasible F G) (answers : Ω → E → Finset E → Bool) (ε : ℝ)
    (one : ∀ q ∈ queries (exactAnswer F) G es,
      probability (fun ω => answers ω q.1 q.2 ≠ exactAnswer F q.1 q.2) ≤ ε) :
    1 - es.length*ε ≤ probability (fun ω => prune (answers ω) G es ∈ F) := by
  let qs := queries (exactAnswer F) G es
  let bad := fun (q : E × Finset E) (ω : Ω) => answers ω q.1 q.2 ≠ exactAnswer F q.1 q.2
  have bound := list_union qs bad ε one
  have success : ∀ ω : Ω, ¬ (∃ q ∈ qs, bad q ω) → prune (answers ω) G es ∈ F := by
    intro ω all
    rw [prune_of_correct_transcript (exactAnswer F) _ _ _]
    · exact prune_recovers F G es cover possible
    · intro q hq
      exact not_not.mp (fun wrong => all ⟨q,hq,wrong⟩)
  have enough := probability_mono success
  rw [probability_not] at enough
  simpa only [qs,queries_length] using (sub_le_sub_left bound 1).trans enough

theorem product_moment {A : Type*} [Fintype A] (f : A → ℝ) (m : ℕ) :
    mean (fun r : Fin m → A => ∏ i, f (r i)) = (mean f)^m := by
  rw [mean,mean,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,div_pow]
  congr 1
  simpa using (Fintype.prod_sum (fun (_ : Fin m) (a : A) => f a)).symm

theorem parity_majority {A : Type} [Fintype A] [Nonempty A] (bad : A → Prop) (r : ℕ)
    (error : probability bad ≤ 1/6) :
    probability (fun a : Fin (2*r) → A => r ≤ (Finset.univ.filter fun i => bad (a i)).card) ≤
      (9/16 : ℝ)^r := by
  classical
  let f := fun a : A => if bad a then (4:ℝ) else 1
  have ef : mean f = 1 + 3*probability bad := by
    conv_lhs =>
      rw [show f = (fun a : A => 1 + 3*(if bad a then (1:ℝ) else 0)) by funext a; dsimp [f];split <;> norm_num]
    rw [probability,← mean_mul_left,mean,Finset.sum_add_distrib,add_div]
    change mean (fun _ : A => 1) + _ = _
    rw [mean_const]
    rfl
  have prod (a : Fin (2*r) → A) : ∏ i, f (a i) = (4:ℝ)^(Finset.univ.filter fun i => bad (a i)).card := by
    simp only [f,← Finset.prod_filter,Finset.prod_const]
  let q := fun a : Fin (2*r) → A => r ≤ (Finset.univ.filter fun i => bad (a i)).card
  have compare : (4:ℝ)^r * probability q ≤ mean (fun a : Fin (2*r) → A => ∏ i, f (a i)) := by
    rw [probability,← mean_mul_left]
    apply mean_mono
    intro a
    rw [prod]
    by_cases h : q a
    · simpa [h] using (pow_le_pow_right₀ (by norm_num : 1 ≤ (4:ℝ)) h)
    · simp [h]
  rw [product_moment,ef] at compare
  have powBound : (1+3*probability bad)^(2*r) ≤ (3/2 : ℝ)^(2*r) := by
    apply pow_le_pow_left₀ _ (by linarith)
    have pos : 0 ≤ probability bad := by rw [probability_eq];positivity
    linarith
  have h := compare.trans powBound
  have algebra : (3/2 : ℝ)^(2*r) = 4^r * (9/16 : ℝ)^r := by
    rw [pow_mul,←mul_pow];norm_num
  rw [algebra] at h
  exact (le_of_mul_le_mul_left h (by positivity : 0 < (4:ℝ)^r))

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open Multidigraph Classical

section Padding

variable {V E A : Type} [Fintype V] [Fintype E] [Fintype A] [DecidableEq V]

private theorem no_start_head {H : Multidigraph V E} {s t : V}
    {P : Fin (Fintype.card V - 1) → E} (hp : P ∈ H.hamPaths s t) (i : Fin (Fintype.card V - 1)) :
    H.head (P i) ≠ s := by
  intro eq
  have zero : i.succ = 0 := (Finset.mem_filter.mp hp).2.2.1 (show H.walkVerts s P i.succ =
    H.walkVerts s P 0 from eq)
  exact Fin.succ_ne_zero i zero

theorem padded_count (H : Multidigraph V E) (decode : A → Option E) (encode : E → A)
    (inverse : ∀ e, decode (encode e) = some e)
    (unique : ∀ a e, decode a = some e → encode e = a)
    (w : E → ℕ) (s t : V) (B : ℤ) :
    (paddedGraph H decode s).weightedPathCount (paddedWeight w decode) s t B =
      H.weightedPathCount w s t B := by
  classical
  symm
  let G := paddedGraph H decode s
  let lift := fun (P : Fin (Fintype.card V-1) → E) i => encode (P i)
  have walk (P) : G.walkVerts s (lift P) = H.walkVerts s P := by
    funext j
    refine Fin.cases rfl (fun i => ?_) j
    simp [G,lift,walkVerts,paddedGraph,paddedHead,inverse]
  have path (P) : lift P ∈ G.hamPaths s t ↔ P ∈ H.hamPaths s t := by
    simp only [hamPaths,Finset.mem_filter,Finset.mem_univ,true_and,IsHamPath,walk]
    simp [G,lift,paddedGraph,paddedTail,inverse]
  have weight (P) : pathWeight (paddedWeight w decode) (lift P) = pathWeight w P := by
    simp [pathWeight,lift,paddedWeight,inverse]
  unfold weightedPathCount
  apply Finset.card_bij (fun P _ => lift P)
  · intro P h
    obtain ⟨hp,hw⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨(path _).2 hp, (weight P) ▸ hw⟩
  · intro P _ Q _ eq
    funext i
    have he := congrArg decode (congrFun eq i)
    simpa [lift,inverse] using he
  · intro Q h
    obtain ⟨hp,hw⟩ := Finset.mem_filter.mp h
    have existsArc (i) : ∃ e, decode (Q i) = some e := by
      cases h : decode (Q i) with
      | some e => exact ⟨e,rfl⟩
      | none =>
        exact (no_start_head hp i (by simp [paddedGraph,paddedHead,h])).elim
    let P := fun i => (existsArc i).choose
    have eq : lift P = Q := funext fun i => unique (Q i) (P i) (existsArc i).choose_spec
    have pathP := (path P).1 (eq ▸ hp)
    have weightP : ((pathWeight w P : ℕ) : ℤ) = B := by
      rw [← weight P,eq];exact hw
    exact ⟨P,Finset.mem_filter.mpr ⟨pathP,weightP⟩,eq⟩

end Padding

variable {n : ℕ} (a : Fin n → Fin n → Prop) [DecidableRel a]

variable (S : SArc a → Finset (Fin 3)) (s : Fin n) (hs : ∀ u, ¬ a u s)

def encodeSlot (x : ArcCopy a S) : Fin (n*n*3) := slotEquiv n (x.1.val,x.2.val)

theorem decode_encode_slot (x : ArcCopy a S) : decodeSlot a S (encodeSlot a S x) = some x := by
  unfold decodeSlot encodeSlot
  rw [Equiv.symm_apply_apply]
  simp only [decodePair,dif_pos x.1.2,dif_pos x.2.2]

theorem encode_decode_slot (i : Fin (n*n*3)) (x : ArcCopy a S) (h : decodeSlot a S i = some x) :
    encodeSlot a S x = i := by
  unfold decodeSlot decodePair at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases Option.some.inj h
  exact (slotEquiv n).apply_symm_apply i

theorem dense_count (t : Fin n) (w : GroupIsolation.Other s × Fin 3 → ℕ) (B : ℤ) :
    (inputGraph a S s).weightedPathCount (inputWeight a S s hs w) s t B =
    (copyGraph a S).weightedPathCount (GroupIsolation.weight a S s hs w) s t B :=
  padded_count _ _ _ (decode_encode_slot a S) (encode_decode_slot a S) _ s t B

theorem dense_max (w : GroupIsolation.Other s × Fin 3 → ℕ) (W : ℕ) (bounded : ∀ x, w x ≤ W) :
    ∀ i, inputWeight a S s hs w i ≤ W := by
  intro i
  unfold inputWeight paddedWeight
  cases decodeSlot a S i with
  | none => exact Nat.zero_le _
  | some x => exact bounded _

theorem dense_degree (w : GroupIsolation.Other s × Fin 3 → ℕ) (v : Fin n) :
    ((inputGraph a S s).incomingWeights (inputWeight a S s hs w) v).card ≤ 3 := by
  classical
  by_cases h : v=s
  · subst v
    have sub : (inputGraph a S s).incomingWeights (inputWeight a S s hs w) s ⊆ {0} := by
      intro k hk
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      have eq : (inputGraph a S s).head i = s := by
        simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
      cases dec : decodeSlot a S i with
      | none => simp [inputWeight,paddedWeight,dec]
      | some x =>
        have bad : x.1.val.2 = s := by simpa [inputGraph,paddedGraph,paddedHead,dec,copyGraph] using eq
        exact ((GroupIsolation.dest a S s hs x).property bad).elim
    exact (Finset.card_le_card sub).trans (by simp)
  · let weights := Finset.univ.image fun l : Fin 3 => w (⟨v,h⟩,l)
    have sub : (inputGraph a S s).incomingWeights (inputWeight a S s hs w) v ⊆ weights := by
      intro k hk
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      have eq : (inputGraph a S s).head i = v := by
        simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
      cases dec : decodeSlot a S i with
      | none =>
        exact (h (by simpa [inputGraph,paddedGraph,paddedHead,dec] using eq.symm)).elim
      | some x =>
        have hv : x.1.val.2 = v := by simpa [inputGraph,paddedGraph,paddedHead,dec,copyGraph] using eq
        apply Finset.mem_image.mpr
        refine ⟨x.2.val,Finset.mem_univ _,?_⟩
        simp [inputWeight,paddedWeight,dec,GroupIsolation.weight,GroupIsolation.dest,hv]
    exact (Finset.card_le_card sub).trans (by simpa [weights] using
      (Finset.card_image_le (s := Finset.univ) (f := fun l : Fin 3 => w (⟨v,h⟩,l))))

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open Multidigraph GroupIsolation FiniteSampling Classical

private theorem probability_instances {A : Type} (i j : Fintype A) (p : A → Prop) :
    @probability A i p = @probability A j p := by
  cases Subsingleton.elim i j
  rfl

theorem probability_table {I J A : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Fintype A] [Nonempty A] (e : I ↪ J) (event : (I → A) → Prop) :
    probability (fun f : J → A => event (fun i => f (e i))) = probability event := by
  classical
  let order := Equiv.ofInjective e e.injective
  let reindex := order.symm.arrowCongr (Equiv.refl A)
  let test := fun f : Set.range e → A => event (reindex f)
  have r := probability_restrict (fun j => j ∈ Set.range e) test
  have u := probability_equiv reindex event
  exact r.trans ((probability_instances _ _ test).trans u)

theorem probability_map_pair {A B U W : Type} [Fintype A] [Fintype B] [Fintype U] [Fintype W]
    (f : A → U) (g : B → W)
    (hf : ∀ p : U → Prop, probability (fun a => p (f a)) = probability p)
    (hg : ∀ p : W → Prop, probability (fun b => p (g b)) = probability p)
    (p : U × W → Prop) :
    probability (fun z : A × B => p (f z.1,g z.2)) = probability p := by
  rw [probability_prod (fun a b => p (f a,g b))]
  have flip (u : U) := hg (fun b => p (u,b))
  simp_rw [flip]

  let F := fun u : U => probability (fun b : W => p (u,b))
  have fiber (a : A) : F (f a) = ∑ u : U, if f a = u then F u else 0 := by simp
  change mean (fun a => F (f a)) = _
  simp_rw [fiber]
  rw [mean_sum (fun u a => if f a = u then F u else 0)]
  have term (u : U) : mean (fun a : A => if f a = u then F u else 0) =
      mean (fun v : U => if v = u then F u else 0) := by
    have eq := congrArg (F u * ·) (hf (fun v => v = u))
    simpa only [probability,←mean_mul_left,mul_ite,mul_one,mul_zero] using eq
  simp_rw [term]
  rw [← mean_sum]
  have right := probability_prod (fun u v => p (u,v))
  calc
    _ = mean F := by simp
    _ = _ := right.symm

theorem restricted_uniform {n : ℕ} (hn : 2 ≤ n) (a : Fin n → Fin n → Prop) [DecidableRel a]
    (s : Fin n) (p : ((SArc a → Fin 50) × (Labels s → Fin (2*labelCount s))) → Prop) :
    probability (fun z : MatrixSeed n => p (restrictedSeed a s z)) = probability p := by
  haveI : NeZero (Wmax n) := ⟨by dsimp [Wmax];omega⟩
  let arcs : SArc a ↪ (Fin n × Fin n) := Function.Embedding.subtype _
  let groups : Labels s ↪ (Fin n × Fin 3) :=
    (Function.Embedding.subtype (fun v : Fin n => v ≠ s)).prodMap (Function.Embedding.refl _)
  let recode := (Equiv.refl (Labels s)).arrowCongr (finCongr (weightRange s))
  let f := fun (z : (Fin n × Fin n) → Fin 50) (j : SArc a) => z (arcs j)
  let g := fun (z : (Fin n × Fin 3) → Fin (Wmax n)) (j : Labels s) => Fin.cast (weightRange s) (z (groups j))
  have valid (pred : (Labels s → Fin (2*labelCount s)) → Prop) :
      probability (fun z => pred (g z)) = probability pred := by
    have proj := probability_table groups (fun f => pred (recode f))
    exact proj.trans (probability_equiv recode pred)
  exact probability_map_pair f g (probability_table arcs) valid p

open Classical in
noncomputable def trueQuery {n : ℕ} (adj : Fin n → Fin n → Bool) (z : Draw n) : Bool :=
  let s := z.1.1
  let t := z.1.2
  let a := pathAdj adj s t
  let seed := restrictedSeed a s z.2.1
  let S := fun e => copyMask (seed.1 e)
  let w := weight a S s (clean_no_in adj s t) (labelWeight s seed.2)
  decide (s ≠ t ∧ adj t s = true ∧ Odd ((copyGraph a S).weightedPathCount w s t z.2.2.val))

private theorem base_of_copied {V : Type} [Fintype V] [DecidableEq V] (a : V → V → Prop) [DecidableRel a]
    {d : ℕ} (S : SArc a → Finset (Fin d)) (s t : V) (w : ArcCopy a S → ℕ) (B : ℤ)
    (odd : Odd ((copyGraph a S).weightedPathCount w s t B)) : ((ofAdj a).hamPaths s t).Nonempty := by
  classical
  have positive : 0 < (copyGraph a S).weightedPathCount w s t B := by
    obtain ⟨k,h⟩ := odd;omega
  obtain ⟨P,mem⟩ := Finset.card_pos.mp positive
  refine ⟨fun i => (P i).1,?_⟩
  have path := (Finset.mem_filter.mp mem).1
  simp only [hamPaths,Finset.mem_filter,Finset.mem_univ,true_and] at path ⊢
  exact path

theorem no_true_query {n : ℕ} (hn : 2 ≤ n) (adj : Fin n → Fin n → Bool) (z : Draw n)
    (h : trueQuery adj z = true) : HasHamCycle n adj := by
  obtain ⟨ends,close,odd⟩ := of_decide_eq_true h
  apply (cycle_iff_closing_path hn adj).2
  exact ⟨z.1.1,z.1.2,ends,close,base_of_copied _ _ _ _ _ _ odd⟩

theorem one_query_mass {n : ℕ} (hn : 2 ≤ n) (adj : Fin n → Fin n → Bool) (cyc : HasHamCycle n adj) :
    (1/2:ℝ)*(49/50:ℝ)^(n-1) ≤ ((n*n*(Bmax n+1):ℕ):ℝ) *
      probability (fun z : Draw n => trueQuery adj z = true) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨s,t,ends,close,path⟩ := (cycle_iff_closing_path hn adj).1 cyc
  let a := pathAdj adj s t
  let hs := clean_no_in adj s t
  let event := fun (r : (SArc a → Fin 50) × (Labels s → Fin (2*labelCount s))) (B : ℕ) =>
    let S := fun e => copyMask (r.1 e)
    Odd ((copyGraph a S).weightedPathCount (weight a S s hs (labelWeight s r.2)) s t B)
  have first := isolated_trial a s t hs ends (fun v h => h.2.1 rfl) (fun v h => h.2.2.2 rfl) path
  change _ ≤ probability (fun r => ∃ B : ℕ, B ≤ (Fintype.card (Fin n)-1)*(2*labelCount s) ∧ event r B) at first
  rw [Fintype.card_fin] at first
  have targetBound : (n-1)*(2*labelCount s) = Bmax n := congrArg ((n-1)*·) (weightRange s).symm
  rw [targetBound] at first
  let any := fun r => ∃ j : Fin (Bmax n+1), event r j.val
  have coerce : (fun r => ∃ B : ℕ, B ≤ Bmax n ∧ event r B) = any := by
    funext r;apply propext
    exact ⟨fun ⟨B,hB,h⟩ => ⟨⟨B,by omega⟩,h⟩,fun ⟨j,h⟩ => ⟨j.val,by omega,h⟩⟩
  rw [coerce,← restricted_uniform hn a s any] at first
  let inner := fun (u : MatrixSeed n) (B : Fin (Bmax n+1)) => event (restrictedSeed a s u) B.val
  have pick := probability_guess inner
  have outer := single_contribution
    (fun st : Fin n × Fin n => fun z : MatrixSeed n × Fin (Bmax n+1) => trueQuery adj (st,z) = true) (s,t)
  have fixed : (fun z : MatrixSeed n × Fin (Bmax n+1) => trueQuery adj ((s,t),z) = true) =
      fun z => inner z.1 z.2 := by
    funext z
    simp [trueQuery,inner,event,a,hs,ends,close]
  rw [fixed] at outer
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] at pick outer ⊢
  calc
    _ ≤ _ := first.trans pick
    _ ≤ _ := (mul_le_mul_of_nonneg_left outer (by positivity)).trans_eq (by ring)

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open Multidigraph FiniteSampling TargetedSamplers Classical

theorem outputBit_eq_of_run {P : Program} {x coins : List Bool} {v : Bool}
    (h : P.Outputs (runTapes x coins) (some [v])) : outputBit P x coins = v := by
  obtain ⟨y,ey,hy⟩ := h
  cases v
  · have no : ¬P.Outputs (runTapes x coins) (some [true]) := by
      rintro ⟨z,ez,hz⟩
      have eq : y=z := Option.some.inj (ey.symm.trans ez)
      subst z;rw [hy] at hz;contradiction
    simp [outputBit,no]
  · simp [outputBit,show P.Outputs (runTapes x coins) (some [true]) from ⟨y,ey,hy⟩]

theorem parity_bit_error (P : Program) (x : List Bool) (L : ℕ) (b : Bool)
    (h : (5/6:ℝ) ≤ outputProb P x L [b]) :
    probability (fun c : Fin L → Bool => outputBit P x (List.ofFn c) ≠ b) ≤ 1/6 := by
  let event := fun c : Fin L → Bool => P.Outputs (runTapes x (List.ofFn c)) (some [b])
  have law : probability event = outputProb P x L [b] := by
    unfold outputProb
    rw [probability_eq]
    simp [event,Fintype.card_fun]
  have mono := probability_mono (p := event) (q := fun c => outputBit P x (List.ofFn c) = b)
    (fun _ h => outputBit_eq_of_run h)
  rw [probability_not]
  linarith

theorem majority_error {A : Type} [Fintype A] [Nonempty A] (estimate : A → Bool)
    (b : Bool) (r : ℕ) (h : probability (fun a => estimate a ≠ b) ≤ 1/6) :
    probability (fun x : Fin (2*r) → A => majority estimate r x ≠ b) ≤ (9/16 : ℝ)^r := by
  refine LE.le.trans ?_ (parity_majority (fun a => estimate a ≠ b) r h)
  apply probability_mono
  intro x bad
  have split := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2*r))))
    (p := fun i => estimate (x i) = true)
  simp only [Finset.card_univ,Fintype.card_fin] at split
  cases b with
  | true =>
    have neg : ¬r < (Finset.univ.filter (fun i => estimate (x i) = true)).card := by
      simpa [majority] using bad
    calc
      r ≤ (Finset.univ.filter (fun i => ¬estimate (x i) = true)).card := by omega
      _ = _ := by apply congrArg Finset.card; ext i; simp
  | false =>
    have pos : r < (Finset.univ.filter (fun i => estimate (x i) = true)).card := by
      simpa [majority] using bad
    simpa using pos.le

noncomputable def parityScale (C : ℝ) (k n : ℕ) :=
  C*(15/8:ℝ)^n*((n+n*n*3+6*(n-1)+1:ℕ):ℝ)^k

variable {n : ℕ} (adj : Fin n → Fin n → Prop) [DecidableRel adj]

variable (S : SArc adj → Finset (Fin 3)) (s t : Fin n) (hs : ∀ u, ¬ adj u s)

variable (w : GroupIsolation.Other s × Fin 3 → ℕ)

theorem dense_oracle : ∃ (P : Program) (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ {n : ℕ} (adj : Fin n → Fin n → Prop) [DecidableRel adj]
      (S : SArc adj → Finset (Fin 3)) (s t : Fin n) (hs : ∀ u, ¬ adj u s) (_ : s ≠ t)
      (w : GroupIsolation.Other s × Fin 3 → ℕ), (∀ j, w j ≤ 6*(n-1)) → ∀ B : ℕ,
      let x := parityInput adj S s t hs w B
      let b := decide (Odd ((copyGraph adj S).weightedPathCount (GroupIsolation.weight adj S s hs w) s t B))
      (∀ coins, ∃ cost, P.RunsIn (runTapes x coins) cost (some [outputBit P x coins]) ∧
        (cost:ℝ) ≤ parityScale C k n) ∧
      (∀ L : ℕ, parityScale C k n ≤ L → ∀ r : ℕ,
        probability (fun c : Fin (2*r) → Fin L → Bool =>
          majority (fun tape : Fin L → Bool => outputBit P x (List.ofFn tape)) r c ≠ b) ≤ (9/16:ℝ)^r) := by
  obtain ⟨P,C,k,pos,alg⟩ := proposition4
  refine ⟨P,C,k,pos,?_⟩
  intro n adj inst S s t hs distinct w bound B x b
  let H := inputGraph adj S s
  let f := inputWeight adj S s hs w
  obtain ⟨always,law⟩ := alg 3 (by decide) n (n*n*3) (6*(n-1)) H.tail H.head f
    (dense_max adj S s hs w _ bound) (dense_degree adj S s hs w) s t distinct B
  have rate : 2-(1/2:ℝ)^3 = 15/8 := by norm_num
  rw [rate] at always law
  constructor
  · intro coins
    obtain ⟨cost,v,run,fast⟩ := always coins
    have output : P.Outputs (runTapes x coins) (some [v]) := by
      obtain ⟨z,halt,_,out⟩ := run
      exact ⟨z,halt,out⟩
    have eq := outputBit_eq_of_run output
    refine ⟨cost,?_,fast⟩
    rw [eq]
    exact run
  · intro L room r
    apply majority_error
    apply parity_bit_error
    have eq := dense_count adj S s hs t w B
    change H.weightedPathCount f s t B = _ at eq
    specialize law L room
    change (5/6:ℝ) ≤ outputProb P x L [decide (Odd (H.weightedPathCount f s t B))] at law
    simpa only [eq] using law

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open Multidigraph GroupIsolation FiniteSampling TargetedSamplers Classical

theorem draw_nonempty {n : ℕ} (hn : 2 ≤ n) : Nonempty (Draw n) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : NeZero (Wmax n) := ⟨by dsimp [Wmax];omega⟩
  infer_instance

noncomputable def idealBit {n : ℕ} (adj : Fin n → Fin n → Bool) (bits : CoinBlock (Draw n)) : Bool :=
  (decodeRank (rankDraw n) bits).elim false (trueQuery adj)

theorem ideal_of_cycle {n : ℕ} (hn : 2 ≤ n) (adj : Fin n → Fin n → Bool) (yes : HasHamCycle n adj) :
    (1/2:ℝ)*(49/50:ℝ)^(n-1) ≤ (2 : ℝ)*(n*n*(Bmax n+1):ℕ)*
        probability (fun bits => idealBit adj bits = true) := by
  haveI := draw_nonempty hn
  have h := padded_event (rankedCode (rankDraw n)) (fun z => trueQuery adj z = true)
  have eq (bits : CoinBlock (Draw n)) :
      (∃ z, rankedCode (rankDraw n) z = bits ∧ trueQuery adj z = true) ↔ idealBit adj bits = true := by
    constructor
    · rintro ⟨z,rfl,ok⟩;simpa [idealBit,decodeRank_code] using ok
    · intro ok
      unfold idealBit at ok
      cases e : decodeRank (rankDraw n) bits with
      | none => simp [e] at ok
      | some z => exact ⟨z,rankedCode_of_decode e,by simpa [e] using ok⟩
  have same := funext (fun bits => propext (eq bits))
  rw [same] at h
  exact (one_query_mass hn adj yes).trans ((mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring))

theorem ideal_implies_cycle {n : ℕ} (hn : 2 ≤ n) (adj : Fin n → Fin n → Bool) (bits : CoinBlock (Draw n))
    (hit : idealBit adj bits = true) : HasHamCycle n adj := by
  unfold idealBit at hit
  cases h : decodeRank (rankDraw n) bits with
  | none => simp [h] at hit
  | some z => exact no_true_query hn adj z (by simpa [h] using hit)

abbrev ParityContract (P : Program) (C : ℝ) (k : ℕ) : Prop :=
  ∀ {n : ℕ} (adj : Fin n → Fin n → Bool) (bits : CoinBlock (Draw n)) (r L : ℕ), parityScale C k n ≤ L →
    probability (fun c => verifiedQuery P adj r L bits c ≠ idealBit adj bits) ≤ (9/16:ℝ)^r

theorem parity_query_exists : ∃ (P : Program) (C : ℝ) (k : ℕ), 0 < C ∧ ParityContract P C k ∧
    ∀ {n : ℕ} (adj : Fin n → Fin n → Bool) (z : Draw n) (x : List Bool), candidateInput adj z = some x →
      ∀ coins, ∃ cost, P.RunsIn (runTapes x coins) cost (some [outputBit P x coins]) ∧
        (cost : ℝ) ≤ parityScale C k n := by
  obtain ⟨P,C,k,pos,run⟩ := dense_oracle
  refine ⟨P,C,k,pos,?_,?_⟩
  · intro n adj bits r L room
    unfold verifiedQuery idealBit
    cases dec : decodeRank (rankDraw n) bits with
    | none => simp [probability_eq];positivity
    | some z =>
      let s := z.1.1
      let t := z.1.2
      let a := pathAdj adj s t
      let seed := restrictedSeed a s z.2.1
      let S := fun e => copyMask (seed.1 e)
      let w := labelWeight s seed.2
      have bound (x) : w x ≤ 6*(n-1) := by
        change (seed.2 x).val+1 ≤ Wmax n
        rw [weightRange s];exact (seed.2 x).isLt
      by_cases valid : s ≠ t ∧ adj t s = true
      · have h := (run a S s t (clean_no_in adj s t) valid.1 w bound z.2.2.val).2 L room r
        have input : candidateInput adj z = some (parityInput a S s t (clean_no_in adj s t) w z.2.2.val) :=
          if_pos valid
        have ans : trueQuery adj z = decide (Odd ((copyGraph a S).weightedPathCount (weight a S s (clean_no_in adj s t) w) s t z.2.2.val)) := by
          let pred := Odd ((copyGraph a S).weightedPathCount (weight a S s (clean_no_in adj s t) w) s t z.2.2.val)
          change decide (s ≠ t ∧ adj t s = true ∧ pred) = decide pred
          by_cases hit : pred
          · rw [decide_eq_true ⟨valid.1,valid.2,hit⟩,decide_eq_true hit]
          · rw [decide_eq_false (show ¬(s ≠ t ∧ adj t s = true ∧ pred) from fun h => hit h.2.2),decide_eq_false hit]
        simp only [Option.bind_some,Option.elim_some,input,ans]
        exact h
      · have empty : candidateInput adj z = none := if_neg valid
        have falseQ : trueQuery adj z = false := by
          apply decide_eq_false
          exact fun h => valid ⟨h.1,h.2.1⟩
        simp [empty,falseQ,probability_eq]; positivity
  · intro n adj z x input coins
    let s := z.1.1
    let t := z.1.2
    let a := pathAdj adj s t
    let seed := restrictedSeed a s z.2.1
    let S := fun e => copyMask (seed.1 e)
    let w := labelWeight s seed.2
    have bound (j) : w j ≤ 6*(n-1) := by
      change (seed.2 j).val+1 ≤ Wmax n
      rw [weightRange s];exact (seed.2 j).isLt
    by_cases valid : s ≠ t ∧ adj t s = true
    · have eq : parityInput a S s t (clean_no_in adj s t) w z.2.2.val = x :=
        Option.some.inj ((if_pos valid).symm.trans input)
      rw [←eq]
      exact (run a S s t (clean_no_in adj s t) valid.1 w bound z.2.2.val).1 coins
    · have no : candidateInput adj z = none := if_neg valid
      simp [no] at input

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open FiniteSampling Classical

theorem ceil_bounds {q : ℚ} (hq : 1 ≤ q) (n : ℕ) :
    (q : ℝ)^n ≤ (⌈q^n⌉₊ : ℕ) ∧ ((⌈q^n⌉₊ : ℕ):ℝ) ≤ 2*(q : ℝ)^n := by
  have one := one_le_pow₀ hq (n := n)
  have lo := Nat.le_ceil (q^n)
  have hi := Nat.ceil_lt_add_one (show 0 ≤ q^n by linarith)
  constructor
  · exact_mod_cast lo
  · exact_mod_cast (show (⌈q^n⌉₊ : ℚ) ≤ 2*q^n by linarith)

theorem enough_coins (C : ℝ) (k n : ℕ) (pos : 0<C) :
    parityScale C k n ≤ coinSpan ⌈C⌉₊ k n := by
  have lower := (ceil_bounds (q := 15/8) (by norm_num) n).1
  rw [show ((15/8:ℚ):ℝ)=15/8 by norm_num] at lower
  unfold parityScale coinSpan
  push_cast
  gcongr
  · exact Nat.le_ceil _

theorem block_covers {n : ℕ} (hn : 2 ≤ n) (adj : Fin n → Fin n → Bool) (cyc : HasHamCycle n adj) :
    (1:ℝ) ≤ (trialBlock n : ℝ) * probability (fun x => idealBit adj x = true) := by
  let mass := probability (fun x => idealBit adj x = true)
  let Q : ℝ := (n*n*(Bmax n+1):ℕ)
  have positive : 0 ≤ mass := by dsimp [mass]; rw [probability_eq];positivity
  have h := ideal_of_cycle hn adj cyc
  change (1/2:ℝ)*(49/50:ℝ)^(n-1) ≤ 2*Q*mass at h
  have hpow : (49/50:ℝ)^n ≤ (49/50:ℝ)^(n-1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.sub_le ..)
  have ceil := (ceil_bounds (q := 50/49) (by norm_num) n).1
  rw [show ((50/49:ℚ):ℝ)=50/49 by norm_num] at ceil
  have ce : (50/49:ℝ)^n ≤ outerCeil n := ceil
  have cancel : (50/49:ℝ)^n*(49/50:ℝ)^n=1 := by rw [←mul_pow];norm_num
  have bound := mul_le_mul_of_nonneg_left (show (49/50:ℝ)^n≤4*Q*mass by linarith) (show 0 ≤ (50/49:ℝ)^n by positivity)
  rw [cancel] at bound
  have qpos : 0 ≤ Q := by dsimp [Q]; positivity
  calc
    1 ≤ (50/49:ℝ)^n * (4*Q*mass) := bound
    _ ≤ (outerCeil n:ℝ) * (4*Q*mass) := mul_le_mul_of_nonneg_right ce (by positivity)
    _ = _ := by unfold trialBlock;push_cast;dsimp [Q,mass];push_cast;ring

theorem parity_union_bound (n : ℕ) :
    (trials n : ℝ)*(9/16:ℝ)^(majorityHalf n) ≤ (1/2:ℝ)^(outerBlocks n) := by
  let M := trials n
  let D := outerBlocks n
  have size : (M:ℝ) ≤ (2:ℝ)^M.size := by exact_mod_cast (Nat.lt_size_self M).le
  have comp : (9/16:ℝ)^(majorityHalf n) ≤ (1/2:ℝ)^(M.size+D) := by
    unfold majorityHalf
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by norm_num : (9/16:ℝ)^2≤1/2) _
  calc
    _ ≤ (2:ℝ)^M.size * (1/2:ℝ)^(M.size+D) := mul_le_mul size comp (by positivity) (by positivity)
    _ = _ := by rw [pow_add,←mul_assoc,←mul_pow];norm_num [D]

theorem edge_union_bound (n : ℕ) :
    (n*n : ℕ) * (2*(1/2:ℝ)^(outerBlocks n)) ≤ 1/3 := by
  let D := outerBlocks n
  have hnat : 6*(n*n) ≤ 2^D := (show 6*(n*n) ≤ D by dsimp [D,outerBlocks];rw [Nat.mul_assoc];omega).trans Nat.lt_two_pow_self.le
  have hr : (6:ℝ)*((n*n:ℕ):ℝ) ≤ 2^D := by exact_mod_cast hnat
  change _ * (2*(1/2:ℝ)^D) ≤ _
  rw [one_div_pow]
  have pos : 0 < (2:ℝ)^D := by positivity
  field_simp
  nlinarith only [hr]

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open Multidigraph FiniteSampling TargetedSamplers Classical

private theorem any_wrong (P : Program) {C : ℝ} {k n L : ℕ} (run : ParityContract P C k)
    (adj : Fin n → Fin n → Bool) (long : parityScale C k n ≤ L) :
    probability (fun z : SeedPanel n L => ∃ i, verifiedQuery P adj (majorityHalf n) L (z.1 i) z.2 ≠ idealBit adj (z.1 i)) ≤
      (1/2:ℝ)^(outerBlocks n) := by
  let bad := fun (x : Fin (trials n) → CoinBlock (Draw n)) (u : Fin (2*majorityHalf n) → Fin L → Bool) =>
    ∃ i, verifiedQuery P adj (majorityHalf n) L (x i) u ≠ idealBit adj (x i)
  change probability (fun z : _ × _ => bad z.1 z.2) ≤ _
  rw [probability_prod bad]
  apply LE.le.trans _ (parity_union_bound n)
  rw [← mean_const (α := Fin (trials n) → CoinBlock (Draw n))
    ((trials n:ℝ)*(9/16:ℝ)^majorityHalf n)]
  apply mean_mono
  intro x
  refine (probability_exists (fun i u => verifiedQuery P adj (majorityHalf n) L (x i) u ≠ idealBit adj (x i))).trans ?_
  calc
    _ ≤ ∑ _ : Fin (trials n), (9/16:ℝ)^majorityHalf n :=
      Finset.sum_le_sum fun i _ => run adj (x i) _ L long
    _ = _ := by simp

theorem two_sided_error (P : Program) {C : ℝ} {k n L : ℕ} (run : ParityContract P C k)
    (hn : 2 ≤ n) (adj : Fin n → Fin n → Bool) (long : parityScale C k n ≤ L) :
    probability (fun coins : SeedPanel n L => twoSided P adj coins ≠ decide (HasHamCycle n adj)) ≤
      2*(1/2:ℝ)^outerBlocks n := by
  let bad := fun z : SeedPanel n L => ∃ i, verifiedQuery P adj (majorityHalf n) L (z.1 i) z.2 ≠ idealBit adj (z.1 i)
  let miss := fun x : Fin (trials n) → CoinBlock (Draw n) => ∀ i, ¬idealBit adj (x i)=true
  have err := any_wrong P run adj long
  change probability bad ≤ _ at err
  by_cases yes : HasHamCycle n adj
  · have noHit := all_miss (fun b => idealBit adj b = true) (trialBlock n) (outerBlocks n) (block_covers hn adj yes)
    have same : probability (fun z : SeedPanel n L => miss z.1) = probability miss := by
      rw [probability_prod (fun a _ => miss a)]
      unfold probability
      apply congrArg mean;funext a;exact mean_const _
    have inclusion : ∀ z : SeedPanel n L, twoSided P adj z ≠ decide (HasHamCycle n adj) → bad z ∨ miss z.1 := by
      intro z wrong
      by_cases b : bad z
      · exact Or.inl b
      · right
        intro i hit
        have eq := not_not.mp (fun h => b ⟨i,h⟩)
        have actual : twoSided P adj z = true := decide_eq_true ⟨i,eq.trans hit⟩
        exact wrong (actual.trans (decide_eq_true yes).symm)
    have both := (probability_mono inclusion).trans (probability_union bad (fun z => miss z.1))
    rw [same] at both
    change probability miss ≤ _ at noHit
    linarith
  · have inclusion : ∀ z : SeedPanel n L, twoSided P adj z ≠ decide (HasHamCycle n adj) → bad z := by
      intro z wrong
      have value : twoSided P adj z = true := by simpa [yes] using wrong
      obtain ⟨i,hi⟩ := of_decide_eq_true value
      refine ⟨i,fun eq => yes (ideal_implies_cycle hn adj (z.1 i) ?_)⟩
      exact eq.symm.trans hi
    have inequality := (probability_mono inclusion).trans err
    have pos : (0:ℝ) ≤ (1/2:ℝ)^outerBlocks n := by positivity
    linarith

@[simp] theorem edges_adjacency {n : ℕ} (G : Finset (Fin n × Fin n)) : edges (adjacency G) = G := by
  ext e;simp [edges,adjacency]

theorem exactAnswer_eq {n : ℕ} (e : Fin n × Fin n) (G : Finset (Fin n × Fin n)) :
    exactAnswer (cycles n) e G = decide (HasHamCycle n (adjacency G)) := by
  have eq := graph_feasible (adjacency G)
  rw [edges_adjacency] at eq
  unfold exactAnswer
  simp only [propext eq]

@[simp] theorem edgeOrder_length (n : ℕ) : (edgeOrder n).length=n*n := by
  simp [edgeOrder,List.length_flatMap]

theorem edgeOrder_mem {n : ℕ} (e : Fin n × Fin n) : e ∈ edgeOrder n := by
  apply List.mem_flatMap.mpr
  refine ⟨e.1,by simp, List.mem_map.mpr ⟨e.2,by simp,rfl⟩⟩

theorem recovery_probability (P : Program) {C : ℝ} {k n L : ℕ} (run : ParityContract P C k)
    (hn : 2 ≤ n) (adj : Fin n → Fin n → Bool) (long : parityScale C k n ≤ L) (yes : HasHamCycle n adj) :
    (2/3:ℝ) ≤ probability (fun z : SeedPanel n L => remaining P adj z ∈ cycles n) := by
  let ans := fun (z : SeedPanel n L) (_ : Fin n × Fin n) (G : Finset (Fin n × Fin n)) => twoSided P (adjacency G) z
  have point (q : (Fin n × Fin n) × Finset (Fin n × Fin n)) :
      probability (fun ω => ans ω q.1 q.2 ≠ exactAnswer (cycles n) q.1 q.2) ≤ 2*(1/2:ℝ)^outerBlocks n := by
    rw [exactAnswer_eq]
    exact two_sided_error P run hn _ long
  have get := prune_probability (cycles n) (edges adj) (edgeOrder n) (fun e _ => edgeOrder_mem e)
    ((graph_feasible adj).mpr yes) ans _ (fun q _ => point q)
  have budget := edge_union_bound n
  rw [edgeOrder_length] at get
  exact (show (2/3:ℝ) ≤ 1 - ((n*n:ℕ):ℝ)*(2*(1/2:ℝ)^outerBlocks n) by linarith).trans get

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open Multidigraph

theorem certify_sound {n : ℕ} (R : Finset (Fin n × Fin n)) (adj : Fin n → Fin n → Bool)
    (sub : R ⊆ edges adj) (ok : certify n R = true) : HasHamCycle n adj := by
  cases n with
  | zero => contradiction
  | succ n =>
    let f := nextVertex R
    let ord (i : Fin (n+1)) := f^[i.val] 0
    obtain ⟨closed,arcs,injective⟩ := of_decide_eq_true ok
    let σ := Equiv.ofBijective ord (Finite.injective_iff_bijective.mp (show Function.Injective ord from fun i j => injective i j))
    refine ⟨Nat.succ_pos _,σ,fun j => ?_⟩
    have follow (i : Fin (n+1)) : f (ord i) = ord (finRotate _ i) := by
      refine Fin.lastCases ?_ (fun v => ?_) i
      · rw [finRotate_last]
        exact (Function.iterate_succ_apply' f n 0).symm.trans closed
      · rw [show finRotate (n+1) v.castSucc = v.succ from finRotate_of_lt v.isLt]
        exact (Function.iterate_succ_apply' f v.val 0).symm
    have hem : (ord j,f (ord j)) ∈ edges adj := sub (arcs j)
    rw [follow] at hem
    exact (Finset.mem_filter.mp hem).2

private theorem next_cycle {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    nextVertex (cycleEdges σ) (σ i) = σ (finRotate n i) := by
  let p := fun v => decide ((σ i,v) ∈ cycleEdges σ)
  have spec (v : Fin n) : p v = true ↔ v=σ (finRotate n i) := by
    simp only [p,decide_eq_true_eq,cycleEdges,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨j,eq⟩
      obtain rfl : j=i := σ.injective (congrArg Prod.fst eq)
      exact (congrArg Prod.snd eq).symm
    · rintro rfl;exact ⟨i,rfl⟩
  have found : ((List.finRange n).find? p).isSome := by
    rw [List.find?_isSome]
    exact ⟨σ (finRotate n i),by simp,(spec _).2 rfl⟩
  cases h : (List.finRange n).find? p with
  | none => simp [h] at found
  | some v =>
    have good : p v = true := List.find?_some h
    change ((List.finRange n).find? p).getD _ = _
    rw [h];exact (spec v).1 good

open Fin.NatCast Fin.CommRing in
theorem certify_cycle {n : ℕ} (R : Finset (Fin n × Fin n)) (hit : R ∈ cycles n) : certify n R = true := by
  classical
  cases n with
  | zero => simp [cycles] at hit
  | succ n =>
    obtain ⟨σ,_,rfl⟩ := Finset.mem_image.mp (show R ∈ Finset.univ.image cycleEdges by simpa [cycles] using hit)
    let f := nextVertex (cycleEdges σ)
    have step (i : Fin (n+1)) : f (σ i) = σ (finRotate _ i) := next_cycle σ i
    have iterate (i : Fin (n+1)) (k : ℕ) : f^[k] (σ i) = σ (i+(k : Fin (n+1))) := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Function.iterate_succ_apply',ih,step,finRotate_apply,Nat.cast_succ,add_assoc]
    let base := σ.symm 0
    have orbit (k : ℕ) : f^[k] 0 = σ (base+(k : Fin (n+1))) := by
      simpa [base] using iterate base k
    apply decide_eq_true
    refine ⟨?_,?_,?_⟩
    · change f^[n+1] 0 = 0
      rw [orbit]
      simp [base]
    · intro i
      change (f^[i.val] 0, f (f^[i.val] 0)) ∈ cycleEdges σ
      rw [orbit,step]
      exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
    · intro i j h
      change f^[i.val] 0 = f^[j.val] 0 at h
      rw [orbit,orbit] at h
      simpa using add_left_cancel (σ.injective h)

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open FiniteSampling TargetedSamplers Classical

theorem answer_sound (P : Program) (A k : ℕ) {n : ℕ} (adj : Fin n → Fin n → Bool) (coins : List Bool) :
    answer P A k adj coins = true → HasHamCycle n adj := by
  unfold answer
  split
  · exact (smallCycleAnswer_correct ‹_› adj).1
  · exact certify_sound _ adj (prune_subset ..)

theorem answer_probability (P : Program) {C : ℝ} {k : ℕ} (run : ParityContract P C k)
    (pos : 0 < C) {n : ℕ} (adj : Fin n → Fin n → Bool) (yes : HasHamCycle n adj)
    (T : ℕ) (room : coinCount n (coinSpan ⌈C⌉₊ k n) ≤ T) :
    (2/3:ℝ) ≤ probability (fun c : Fin T → Bool => answer P ⌈C⌉₊ k adj (List.ofFn c) = true) := by
  by_cases small : n ≤ 1
  · have yesSmall := (smallCycleAnswer_correct small adj).2 yes
    simp [answer,small,yesSmall,probability,mean_const]
    norm_num
  · let L := coinSpan ⌈C⌉₊ k n
    let valid := fun (z : SeedPanel n L) => certify n (remaining P adj z) = true
    have recovery := recovery_probability P run (by omega : 2≤n) adj (enough_coins C k n pos) yes
    have math : (2/3:ℝ) ≤ probability valid :=
      recovery.trans (probability_mono (fun z h => certify_cycle _ h))
    have law := probability_equiv (panelEquiv n L) valid
    have pad := probability_prefix room (fun c => valid (panelEquiv n L c))
    refine math.trans_eq ((law.symm.trans pad.symm).trans ?_)
    apply congrArg probability
    funext c
    unfold answer
    rw [if_neg small]
    change valid (panelEquiv n L _) = valid (panelFromTape n L (List.ofFn c))
    apply congrArg valid
    apply congrArg (panelEquiv n L)
    funext i
    simp [show i.val < T by omega] <;> rfl

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open FiniteSampling TargetedSamplers Classical

theorem finite_search : ∃ (Q : Program) (A k : ℕ), QueryTime Q A k ∧
    ∀ (n : ℕ) (adj : Fin n → Fin n → Bool),
      (n≤1 → ∀ c, answer Q A k adj c = smallCycleAnswer n adj) ∧
      (∀ c, answer Q A k adj c = true → HasHamCycle n adj) ∧
      (HasHamCycle n adj → ∀ L : ℕ, coinCount n (coinSpan A k n) ≤ L →
        (2/3:ℝ) ≤ acceptsFraction (answer Q A k adj) L) := by
  obtain ⟨Q,C,k,pos,prob,run⟩ := parity_query_exists
  refine ⟨Q,⌈C⌉₊,k,?_,?_⟩
  · intro n adj z x valid c
    obtain ⟨cost,ok,bound⟩ := run adj z x valid c
    exact ⟨cost,ok,by exact_mod_cast bound.trans (enough_coins C k n pos)⟩
  · intro n adj
    refine ⟨fun h c => if_pos h,answer_sound _ _ _ _,?_⟩
    intro yes L long
    have low := answer_probability Q prob pos adj yes L long
    refine low.trans_eq ?_
    rw [probability_eq]
    unfold acceptsFraction
    apply congrArg₂ (fun a b : ℝ => a/b)
    · apply congrArg (fun z : ℕ => (z:ℝ))
      apply congrArg Finset.card
      ext i
      simp
    · simp [Fintype.card_fun]

end DirectedHamiltonicity.Main.CycleReduction

end

open TargetedSamplers DirectedHamiltonicity.Main DirectedHamiltonicity.Main.CycleReduction

theorem solution : ∃ (Q : Program) (A k : ℕ), QueryTime Q A k ∧
    ∀ (n : ℕ) (adj : Fin n → Fin n → Bool),
      (n≤1 → ∀ c, answer Q A k adj c = smallCycleAnswer n adj) ∧
      (∀ c, answer Q A k adj c = true → HasHamCycle n adj) ∧
      (HasHamCycle n adj → ∀ L : ℕ, coinCount n (coinSpan A k n) ≤ L →
        (2/3:ℝ) ≤ acceptsFraction (answer Q A k adj) L) := by
  exact DirectedHamiltonicity.Main.CycleReduction.finite_search
