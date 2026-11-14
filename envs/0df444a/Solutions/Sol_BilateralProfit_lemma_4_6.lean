-- Prove2me | solution 1 for BilateralProfit.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-13T16:41:05.831566+00:00
-- url     : https://prove2.me/submissions/1301ff4f-7272-4713-851d-df71fa138b8f

import Mathlib
import Definitions.Def_BilateralProfit_OneRound
import Theorems.Thm_BilateralProfit_proposition_4_7
import Theorems.Thm_SinkhornHall_lemma_1_1


namespace BilateralProfit.OneRoundTrade46

open MeasureTheory

variable {K : ℕ}

theorem coord_mem (hK : 0 < K) (i : Fin (K + 1)) :
    (i : ℝ) / K ∈ Set.Icc (0 : ℝ) 1 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hi : (i : ℕ) ≤ K := by omega
  constructor
  · positivity
  · apply (div_le_one hKr).mpr
    exact_mod_cast hi

theorem pt_mem (hK : 0 < K) (x : Grid K) :
    pt K x ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
  ⟨coord_mem hK x.1, coord_mem hK x.2⟩

theorem spread_mem (hK : 0 < K) (a : Act K) :
    (pt K a.1).2 - (pt K a.1).1 ∈ Set.Icc (0 : ℝ) 1 := by
  have hleft := coord_mem hK a.1.1
  have hright := coord_mem hK a.1.2
  have horder : ((a.1.1 : ℕ) : ℝ) ≤ ((a.1.2 : ℕ) : ℝ) := by exact_mod_cast a.2
  have hdiv := div_le_div_of_nonneg_right horder (by positivity : (0 : ℝ) ≤ K)
  change ((a.1.2 : ℕ) : ℝ) / K - ((a.1.1 : ℕ) : ℝ) / K ∈ Set.Icc 0 1
  exact ⟨sub_nonneg.mpr hdiv, by linarith [hleft.1, hright.2]⟩


end BilateralProfit.OneRoundTrade46


namespace BilateralProfit.OneRoundInfo46

variable {K : ℕ}

theorem marg_nonneg (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a' : Act K) :
    0 ≤ margA ρ a' := Finset.sum_nonneg (fun v _ => hρ.1 (v, a'))

theorem joint_nonneg (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (z : Bool) : 0 ≤ jointP ρ a a' z := by
  classical
  unfold jointP
  apply Finset.sum_nonneg
  intro v _
  split_ifs <;> first | exact hρ.1 _ | exact le_rfl

theorem true_add_false (ρ : Grid K × Act K → ℝ) (a a' : Act K) :
    jointP ρ a a' true + jointP ρ a a' false = margA ρ a' := by
  classical
  unfold jointP margA
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : Trades (pt K v) (pt K a.1) <;> simp [hv]

theorem row_sum (ρ : Grid K × Act K → ℝ) (a a' : Act K) :
    ∑ z : Bool, jointP ρ a a' z = margA ρ a' := by
  simpa only [Fintype.sum_bool] using true_add_false ρ a a'

theorem marg_sum (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) :
    ∑ a', margA ρ a' = 1 := by
  unfold margA
  rw [Finset.sum_comm]
  simpa only [Fintype.sum_prod_type] using hρ.2

theorem joint_sum (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : Act K) :
    ∑ a', ∑ z : Bool, jointP ρ a a' z = 1 := by
  simp_rw [row_sum]
  exact marg_sum ρ hρ

theorem z_nonneg (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : Act K) (z : Bool) :
    0 ≤ zP ρ a z := Finset.sum_nonneg (fun a' _ => joint_nonneg ρ hρ a a' z)

theorem z_sum (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : Act K) :
    ∑ z : Bool, zP ρ a z = 1 := by
  unfold zP
  rw [Finset.sum_comm]
  exact joint_sum ρ hρ a

theorem joint_le_marg (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (z : Bool) : jointP ρ a a' z ≤ margA ρ a' := by
  have h := true_add_false ρ a a'
  have ht := joint_nonneg ρ hρ a a' true
  have hf := joint_nonneg ρ hρ a a' false
  cases z <;> linarith

theorem joint_le_z (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (z : Bool) : jointP ρ a a' z ≤ zP ρ a z := by
  exact Finset.single_le_sum (fun b _ => joint_nonneg ρ hρ a b z) (Finset.mem_univ a')

theorem joint_zero_of_marg_zero (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (hm : margA ρ a' = 0) (z : Bool) : jointP ρ a a' z = 0 := by
  have hn := joint_nonneg ρ hρ a a' z
  have hl := joint_le_marg ρ hρ a a' z
  linarith

theorem joint_zero_of_z_zero (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (z : Bool) (hz : zP ρ a z = 0) : jointP ρ a a' z = 0 := by
  have hn := joint_nonneg ρ hρ a a' z
  have hl := joint_le_z ρ hρ a a' z
  linarith

theorem joint_pos_marg_pos (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (z : Bool) (hj : 0 < jointP ρ a a' z) : 0 < margA ρ a' :=
  hj.trans_le (joint_le_marg ρ hρ a a' z)

theorem joint_pos_z_pos (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (z : Bool) (hj : 0 < jointP ρ a a' z) : 0 < zP ρ a z :=
  hj.trans_le (joint_le_z ρ hρ a a' z)

theorem joint_true (ρ : Grid K × Act K → ℝ) (a a' : Act K) :
    jointP ρ a a' true = ∑ v, ρ (v, a') * tradeBit (pt K v) (pt K a.1) := by
  classical
  unfold jointP
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : Trades (pt K v) (pt K a.1) <;> simp [tradeBit, hv]

theorem z_true (ρ : Grid K × Act K → ℝ) (a : Act K) :
    zP ρ a true = P0 ρ (pt K a.1) := by
  unfold zP P0
  simp_rw [joint_true]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_prod_type]

theorem z_false (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : Act K) :
    zP ρ a false = 1 - P0 ρ (pt K a.1) := by
  have h := z_sum ρ hρ a
  simp only [Fintype.sum_bool, z_true] at h
  linarith

theorem cond_true (ρ : Grid K × Act K → ℝ) (a a' : Act K) :
    jointP ρ a a' true / margA ρ a' = Pcond ρ a' (pt K a.1) := by
  rw [joint_true]
  rfl

theorem cond_false (ρ : Grid K × Act K → ℝ) (a a' : Act K) (hm : margA ρ a' ≠ 0) :
    jointP ρ a a' false / margA ρ a' = 1 - Pcond ρ a' (pt K a.1) := by
  have h := true_add_false ρ a a'
  rw [← cond_true]
  apply (div_eq_iff hm).mpr
  field_simp
  linarith

theorem cond_nonneg (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a a' : Act K) :
    0 ≤ Pcond ρ a' (pt K a.1) := by
  rw [← cond_true]
  exact div_nonneg (joint_nonneg ρ hρ a a' true) (marg_nonneg ρ hρ a')

theorem cond_le_one (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a a' : Act K) :
    Pcond ρ a' (pt K a.1) ≤ 1 := by
  rw [← cond_true]
  by_cases hm : margA ρ a' = 0
  · simp [hm]
  · exact (div_le_one (lt_of_le_of_ne (marg_nonneg ρ hρ a') (Ne.symm hm))).mpr
      (joint_le_marg ρ hρ a a' true)

theorem p0_nonneg (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : Act K) :
    0 ≤ P0 ρ (pt K a.1) := by rw [← z_true]; exact z_nonneg ρ hρ a true

theorem p0_le_one (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : Act K) :
    P0 ρ (pt K a.1) ≤ 1 := by
  have h := z_nonneg ρ hρ a false
  rw [z_false ρ hρ a] at h
  linarith

theorem cond_zero_of_p0_zero (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (hp : P0 ρ (pt K a.1) = 0) : Pcond ρ a' (pt K a.1) = 0 := by
  rw [← cond_true, joint_zero_of_z_zero ρ hρ a a' true (by rw [z_true, hp]), zero_div]

theorem cond_one_of_p0_one (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (hm : margA ρ a' ≠ 0) (hp : P0 ρ (pt K a.1) = 1) :
    Pcond ρ a' (pt K a.1) = 1 := by
  have hz : zP ρ a false = 0 := by rw [z_false ρ hρ a, hp]; ring
  have hj := joint_zero_of_z_zero ρ hρ a a' false hz
  have hc := cond_false ρ a a' hm
  rw [hj, zero_div] at hc
  linarith

end BilateralProfit.OneRoundInfo46

namespace BilateralProfit.OneRoundProgram46

open CapacitatedAssort.General

variable {α β : Type}

/-- The returned value is independent of the initial operation counter. -/
def Value (m : Work α) (v : α) : Prop := ∀ s, (m.run s).1 = v

theorem value_pure (v : α) : Value (pure v : Work α) v := by
  intro s
  rfl

theorem value_charge (n : ℕ) : Value (charge n) () := by
  intro s
  rfl

theorem value_bind {m : Work α} {v : α} {f : α → Work β} {w : β}
    (hm : Value m v) (hf : Value (f v) w) : Value (m >>= f) w := by
  intro s
  change ((f (m.run s).1).run (m.run s).2).1 = w
  rw [hm s]
  exact hf _

/-- A list loop with deterministic yield values has the corresponding pure fold value. -/
theorem forIn_value (l : List α) (f : α → β → Work (ForInStep β))
    (g : α → β → β)
    (hf : ∀ x ∈ l, ∀ b, Value (f x b) (.yield (g x b))) (b : β) :
    Value (forIn l b f) (l.foldl (fun b x => g x b) b) := by
  induction l generalizing b with
  | nil =>
      intro s
      rfl
  | cons x l ih =>
      rw [List.forIn_cons]
      intro s
      change ((match (f x b).run s |>.1 with
        | .done b => pure b
        | .yield b => forIn l b f).run ((f x b).run s).2).1 = _
      rw [hf x (by simp) b s]
      exact ih (fun y hy => hf y (by simp [hy])) (g x b) _

theorem foldl_add_value (l : List α) (v : α → ℝ) (s : ℝ) :
    l.foldl (fun s x => s + v x) s = s + (l.map v).sum := by
  induction l generalizing s with
  | nil => simp
  | cons x l ih => simp [ih, add_assoc]

theorem sumW_value (l : List α) (f : α → Work ℝ) (v : α → ℝ)
    (hf : ∀ x ∈ l, Value (f x) (v x)) : Value (sumW l f) ((l.map v).sum) := by
  unfold sumW
  apply value_bind (value_charge 1)
  change Value (forIn l (0 : ℝ) (fun x s => do
    charge 2
    let y ← f x
    pure (ForInStep.yield (s + y)))) _
  have h := forIn_value l (fun x s => do
      charge 2
      let y ← f x
      pure (ForInStep.yield (s + y))) (fun x s => s + v x) (by
    intro x hx s
    apply value_bind (value_charge 2)
    exact value_bind (hf x hx) (value_pure _)) 0
  simpa only [foldl_add_value, zero_add] using h

theorem lookup_foldl_cons [DecidableEq α] (l : List α) (v : α → ℝ)
    (acc : List (α × ℝ)) (x : α) :
    (l.foldl (fun acc y => (y, v y) :: acc) acc).lookup x =
      if x ∈ l then some (v x) else acc.lookup x := by
  induction l generalizing acc with
  | nil => simp
  | cons y l ih =>
      rw [List.foldl_cons, ih]
      by_cases hx : x ∈ l
      · simp [hx]
      · by_cases hxy : y = x
        · subst y
          simp [hx]
        · have hbeq : (x == y) = false := beq_eq_false_iff_ne.mpr (Ne.symm hxy)
          simp [hx, hxy, Ne.symm hxy, List.lookup_cons, hbeq]

theorem tab_value [DecidableEq α] (l : List α) (f : α → Work ℝ) (v : α → ℝ)
    (hf : ∀ x ∈ l, Value (f x) (v x)) :
    Value (tab l f) (fun x => if x ∈ l then v x else 0) := by
  unfold tab
  apply value_bind (value_charge 1)
  have h := forIn_value l (fun x acc => do
      charge 2
      let y ← f x
      pure (ForInStep.yield ((x, y) :: acc)))
    (fun x acc => (x, v x) :: acc) (by
      intro x hx acc
      apply value_bind (value_charge 2)
      exact value_bind (hf x hx) (value_pure _)) []
  have hh := value_bind (f := fun acc : List (α × ℝ) =>
    pure (fun x => (acc.lookup x).getD 0)) h (value_pure _)
  convert hh using 1
  funext x
  rw [lookup_foldl_cons l v [] x]
  split_ifs <;> rfl

theorem tab_value_total [DecidableEq α] (l : List α) (hl : ∀ x, x ∈ l)
    (f : α → Work ℝ) (v : α → ℝ) (hf : ∀ x ∈ l, Value (f x) (v x)) :
    Value (tab l f) v := by
  simpa only [if_pos (hl _)] using tab_value l f v hf

theorem mem_gridList (K : ℕ) (x : Grid K) : x ∈ gridList K := by
  rcases x with ⟨i,j⟩
  simp [gridList]

theorem mem_actList (K : ℕ) (a : Act K) : a ∈ actList K := by
  classical
  simp only [actList, List.mem_filterMap]
  refine ⟨a.1, mem_gridList K a.1, ?_⟩
  simp [a.2]

theorem mem_tableList (K : ℕ) (x : Grid K × Act K) : x ∈ tableList K := by
  simp only [tableList, List.mem_flatMap, List.mem_map]
  exact ⟨x.1, mem_gridList K x.1, x.2, mem_actList K x.2, rfl⟩

theorem nodup_gridList (K : ℕ) : (gridList K).Nodup := by
  change ((List.finRange (K + 1)).product (List.finRange (K + 1))).Nodup
  exact (List.nodup_finRange _).product (List.nodup_finRange _)

theorem nodup_actList (K : ℕ) : (actList K).Nodup := by
  classical
  apply List.Nodup.filterMap ?_ (nodup_gridList K)
  intro x y a hx hy
  split_ifs at hx with hp
  · split_ifs at hy with hq
    · simp only [Option.mem_def, Option.some.injEq] at hx hy
      exact congrArg Subtype.val (hx.trans hy.symm)
    · simp at hy
  · simp at hx

theorem nodup_tableList (K : ℕ) : (tableList K).Nodup := by
  change ((gridList K).product (actList K)).Nodup
  exact (nodup_gridList K).product (nodup_actList K)

theorem sum_list_total [Fintype α] [DecidableEq α] (l : List α)
    (hn : l.Nodup) (hc : ∀ x, x ∈ l) (v : α → ℝ) :
    (l.map v).sum = ∑ x, v x := by
  have hset : l.toFinset = Finset.univ := by
    ext x
    simp [hc x]
  have h := List.sum_toFinset v hn
  rw [hset] at h
  exact h.symm

theorem sum_gridList (K : ℕ) (v : Grid K → ℝ) :
    ((gridList K).map v).sum = ∑ x, v x :=
  sum_list_total _ (nodup_gridList K) (mem_gridList K) v

theorem sum_actList (K : ℕ) (v : Act K → ℝ) :
    ((actList K).map v).sum = ∑ x, v x :=
  sum_list_total _ (nodup_actList K) (mem_actList K) v

theorem sum_tableList (K : ℕ) (v : Grid K × Act K → ℝ) :
    ((tableList K).map v).sum = ∑ x, v x :=
  sum_list_total _ (nodup_tableList K) (mem_tableList K) v

end BilateralProfit.OneRoundProgram46

namespace BilateralProfit.OneRoundSelection46

noncomputable def pick {β : Type} (candidate : β × ℝ)
    (best : Option (β × ℝ)) : Option (β × ℝ) :=
  match best with
  | none => some candidate
  | some old => if candidate.2 < old.2 then some candidate else some old

lemma fold_pick_eq_argmin {α β : Type} (c : α → β × ℝ) (l : List α) :
    l.foldl (fun best x => pick (c x) best) none = (l.map c).argmin Prod.snd := by
  rw [List.argmin, List.foldl_map]
  congr 1
  funext best x
  cases best <;> rfl

lemma fold_pick_min {α β : Type} (c : α → β × ℝ) (l : List α) (hl : l ≠ []) :
    ∃ a ∈ l,
      l.foldl (fun best x => pick (c x) best) none = some (c a) ∧
        ∀ b ∈ l, (c a).2 ≤ (c b).2 := by
  classical
  have hne : (l.map c).argmin Prod.snd ≠ none := by
    intro h
    have hnil : l.map c = [] := List.argmin_eq_none.mp h
    exact hl (List.map_eq_nil_iff.mp hnil)
  rcases harg : (l.map c).argmin Prod.snd with _ | chosen
  · exact (hne harg).elim
  have hmem : chosen ∈ l.map c := List.argmin_mem harg
  obtain ⟨a, ha, hac⟩ := List.mem_map.mp hmem
  refine ⟨a, ha, ?_, ?_⟩
  · rw [fold_pick_eq_argmin, harg, hac]
  · intro b hb
    have hcb : c b ∈ l.map c := List.mem_map.mpr ⟨b, hb, rfl⟩
    simpa [hac] using List.le_of_mem_argmin hcb harg

lemma fold_pick_getD_min {α β : Type} (c : α → β × ℝ) (l : List α) (hl : l ≠ [])
    (fallback : β × ℝ) :
    ∃ a ∈ l,
      (l.foldl (fun best x => pick (c x) best) none).getD fallback = c a ∧
        ∀ b ∈ l, (c a).2 ≤ (c b).2 := by
  obtain ⟨a, ha, hfold, hmin⟩ := fold_pick_min c l hl
  exact ⟨a, ha, by rw [hfold]; rfl, hmin⟩

end BilateralProfit.OneRoundSelection46


namespace BilateralProfit.OneRoundSubmission46

open MeasureTheory

theorem nA_ge_one (K : ℕ) : (1 : ℝ) ≤ nA K := by
  have h : 0 < Fintype.card (Act K) := Fintype.card_pos_iff.mpr inferInstance
  unfold nA
  exact_mod_cast (Nat.succ_le_iff.mpr h)

theorem nA_pos (K : ℕ) : 0 < nA K := lt_of_lt_of_le zero_lt_one (nA_ge_one K)

theorem nG_eq (K : ℕ) : nG K = ((K : ℝ) + 1) ^ 2 := by
  simp [nG, Grid, Fintype.card_prod, Fintype.card_fin, pow_two]

theorem beta_nonneg (K : ℕ) : 0 ≤ beta K := by unfold beta; positivity

theorem base_ge_one (K : ℕ) : (1 : ℝ) ≤ nA K * (1 + beta K * K) := by
  have hA := nA_ge_one K
  have hβ := beta_nonneg K
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  exact le_trans hA (le_mul_of_one_le_right (by positivity) (by nlinarith))

theorem base_pos (K : ℕ) : 0 < nA K * (1 + beta K * K) :=
  zero_lt_one.trans_le (base_ge_one K)

theorem floor_pos (K : ℕ) : 0 < wFloor K := one_div_pos.mpr (base_pos K)

theorem H_ge_one (K : ℕ) : (1 : ℝ) ≤ Hpar K := by
  have hlog := Real.log_nonneg (base_ge_one K)
  unfold Hpar
  have hβ := beta_nonneg K
  nlinarith

theorem H_pos (K : ℕ) : 0 < Hpar K := zero_lt_one.trans_le (H_ge_one K)

theorem eta_pos {K : ℕ} (hK : 0 < K) : 0 < eta K := by
  unfold eta
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hH := H_pos K
  positivity

theorem eta_times_H {K : ℕ} (hK : 0 < K) :
    eta K * Hpar K = 1 / (2 * K * Hpar K) := by
  unfold eta
  field_simp [(Nat.cast_pos.mpr hK : (0 : ℝ) < K).ne', (H_pos K).ne']

theorem eta_times_H_le_half {K : ℕ} (hK : 0 < K) : eta K * Hpar K ≤ 1 / 2 := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hH := H_ge_one K
  rw [eta_times_H hK]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * K * Hpar K) (by norm_num : (0 : ℝ) < 2)).mpr
  nlinarith

theorem log_size_pos {K : ℕ} (hK : 0 < K) : 0 < Real.log (nA K * nG K) := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hA := nA_ge_one K
  have hG : (4 : ℝ) ≤ nG K := by rw [nG_eq]; nlinarith
  apply Real.log_pos
  nlinarith

theorem J_pos {K : ℕ} (hK : 0 < K) : 0 < Jpar K := by
  unfold Jpar
  apply Nat.one_le_ceil_iff.mpr
  have hlog := log_size_pos hK
  have hH := H_pos K
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  positivity

theorem regret_budget {K : ℕ} (hK : 0 < K) :
    Real.log (nA K * nG K) / (eta K * Jpar K) + eta K * Hpar K ^ 2 ≤ 1 / K := by
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hH := H_pos K
  have hη := eta_pos hK
  have hJ : (0 : ℝ) < Jpar K := Nat.cast_pos.mpr (J_pos hK)
  have hηJ : 2 * K * Real.log (nA K * nG K) ≤ eta K * Jpar K := by
    calc
      _ = eta K * (4 * (K : ℝ) ^ 2 * Hpar K ^ 2 * Real.log (nA K * nG K)) := by
        unfold eta
        field_simp [hKr.ne', hH.ne']
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.le_ceil _) hη.le
  have hdiv : Real.log (nA K * nG K) / (eta K * Jpar K) ≤ 1 / (2 * K) := by
    apply (div_le_div_iff₀ (by positivity : 0 < eta K * Jpar K) (by positivity : (0 : ℝ) < 2 * K)).mpr
    nlinarith
  have hterm : eta K * Hpar K ^ 2 = 1 / (2 * K) := by
    unfold eta
    field_simp [hKr.ne', hH.ne']
  rw [hterm]
  calc
    Real.log (nA K * nG K) / (eta K * Jpar K) + 1 / (2 * K) ≤
        1 / (2 * (K : ℝ)) + 1 / (2 * (K : ℝ)) := by linarith
    _ = 1 / (K : ℝ) := by ring

end BilateralProfit.OneRoundSubmission46

namespace BilateralProfit.OneRoundSubmission46

variable {K : ℕ}

noncomputable def update (ρ : Grid K × Act K → ℝ) (a : Act K) (z : Bool) (a' : Act K) : ℝ :=
  (beta K * K * (jointP ρ a a' z / zP ρ a z) + 1 / nA K) / (1 + beta K * K)

noncomputable def proposal (ρ : Grid K × Act K → ℝ) (a : Act K) : Proposal K :=
  (a, update ρ a false, update ρ a true)

noncomputable def expectedScore (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ) (P : Proposal K) : ℝ :=
  ∑ x, ρ x * hScore w P x.1 x.2

theorem uniform_sum (K : ℕ) : (∑ a' : Act K, 1 / nA K) = 1 := by
  rw [Finset.sum_const, nsmul_eq_mul]
  change nA K * (1 / nA K) = 1
  field_simp [(nA_pos K).ne']

theorem update_floor (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a a' : Act K) (z : Bool) :
    wFloor K ≤ update ρ a z a' := by
  have hn : 0 ≤ beta K * K * (jointP ρ a a' z / zP ρ a z) :=
    mul_nonneg (mul_nonneg (beta_nonneg K) (Nat.cast_nonneg K))
      (div_nonneg (OneRoundInfo46.joint_nonneg ρ hρ a a' z) (OneRoundInfo46.z_nonneg ρ hρ a z))
  have hd : 0 < 1 + beta K * K := by
    have := mul_nonneg (beta_nonneg K) (Nat.cast_nonneg K)
    linarith
  have h := div_le_div_of_nonneg_right (show 1 / nA K ≤
      beta K * K * (jointP ρ a a' z / zP ρ a z) + 1 / nA K by linarith) hd.le
  unfold update
  calc
    wFloor K = 1 / nA K / (1 + beta K * K) := by simp only [wFloor, div_div]
    _ ≤ _ := h

theorem trade_at_bottom_top (hK : 0 < K) (a : Act K) :
    Trades (pt K (0, Fin.last K)) (pt K a.1) := by
  have hKr : (K : ℝ) ≠ 0 := (Nat.cast_pos.mpr hK).ne'
  have hp := (OneRoundTrade46.coord_mem hK a.1.1).1
  have hq := (OneRoundTrade46.coord_mem hK a.1.2).2
  simpa [Trades, pt, hKr] using And.intro hp hq

theorem not_trade_at_top_bottom (hK : 0 < K) (a : Act K) :
    ¬Trades (pt K (Fin.last K, 0)) (pt K a.1) := by
  have hKr : (K : ℝ) ≠ 0 := (Nat.cast_pos.mpr hK).ne'
  intro ht
  have horder : ((a.1.1 : ℕ) : ℝ) / K ≤ ((a.1.2 : ℕ) : ℝ) / K :=
    div_le_div_of_nonneg_right (by exact_mod_cast a.2) (Nat.cast_nonneg K)
  simp only [Trades, pt, Fin.val_last, Fin.val_zero, Nat.cast_zero, zero_div, div_self hKr] at ht
  linarith

theorem joint_pos (hK : 0 < K) (ρ : Grid K × Act K → ℝ)
    (hρpos : ∀ x, 0 < ρ x) (a a' : Act K) (z : Bool) : 0 < jointP ρ a a' z := by
  classical
  have hnonneg (v : Grid K) :
      0 ≤ if (Trades (pt K v) (pt K a.1) ↔ z = true) then ρ (v, a') else 0 := by
    split_ifs <;> first | exact (hρpos _).le | exact le_rfl
  cases z with
  | false =>
      have hmem := Finset.single_le_sum (fun v _ => hnonneg v) (Finset.mem_univ (Fin.last K, 0))
      have htrade := not_trade_at_top_bottom hK a
      simp only [Bool.false_eq_true, iff_false, if_pos htrade] at hmem
      simpa only [jointP, Bool.false_eq_true, iff_false] using (hρpos ((Fin.last K, 0), a')).trans_le hmem
  | true =>
      have hmem := Finset.single_le_sum (fun v _ => hnonneg v) (Finset.mem_univ (0, Fin.last K))
      have htrade := trade_at_bottom_top hK a
      simp only [iff_true, if_pos htrade] at hmem
      simpa only [jointP, iff_true] using (hρpos ((0, Fin.last K), a')).trans_le hmem

theorem z_pos (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (hρpos : ∀ x, 0 < ρ x) (a : Act K) (z : Bool) : 0 < zP ρ a z :=
  (joint_pos hK ρ hρpos a default z).trans_le (OneRoundInfo46.joint_le_z ρ hρ a default z)

theorem marg_pos (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (hρpos : ∀ x, 0 < ρ x) (a' : Act K) : 0 < margA ρ a' :=
  (joint_pos hK ρ hρpos default a' true).trans_le (OneRoundInfo46.joint_le_marg ρ hρ default a' true)

theorem update_isDist (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (hρpos : ∀ x, 0 < ρ x) (a : Act K) (z : Bool) : IsDist (update ρ a z) := by
  have hz := z_pos hK ρ hρ hρpos a z
  constructor
  · intro a'
    exact (floor_pos K).le.trans (update_floor ρ hρ a a' z)
  · unfold update
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
    change (beta K * K * (zP ρ a z / zP ρ a z) + ∑ a' : Act K, 1 / nA K) /
      (1 + beta K * K) = 1
    rw [div_self hz.ne', mul_one, uniform_sum]
    have hd : 1 + beta K * K ≠ 0 := by
      have := mul_nonneg (beta_nonneg K) (Nat.cast_nonneg K)
      positivity
    simpa only [add_comm] using div_self hd

theorem dist_le_one {A : Type} [Fintype A] (w : A → ℝ) (hw : IsDist w) (a : A) : w a ≤ 1 :=
  (Finset.single_le_sum (fun i _ => hw.1 i) (Finset.mem_univ a)).trans_eq hw.2

theorem log_weight_bounds (w : Act K → ℝ) (hw : IsDist w) (hwf : ∀ a, wFloor K ≤ w a)
    (a : Act K) :
    -Real.log (nA K * (1 + beta K * K)) ≤ Real.log (w a) ∧ Real.log (w a) ≤ 0 := by
  have hwpos := (floor_pos K).trans_le (hwf a)
  constructor
  · have h := Real.log_le_log (floor_pos K) (hwf a)
    simpa only [wFloor, Real.log_div one_ne_zero (base_pos K).ne', Real.log_one, zero_sub] using h
  · simpa only [Real.log_one] using Real.log_le_log hwpos (dist_le_one w hw a)

theorem score_abs_le (hK : 0 < K) (w : Act K → ℝ) (hw : IsDist w)
    (hwf : ∀ a, wFloor K ≤ w a) (P : Proposal K)
    (hP₀ : IsDist P.2.1) (hP₁ : IsDist P.2.2)
    (hPf₀ : ∀ a, wFloor K ≤ P.2.1 a) (hPf₁ : ∀ a, wFloor K ≤ P.2.2 a)
    (v : Grid K) (a' : Act K) : |hScore w P v a'| ≤ Hpar K := by
  have hwpos := (floor_pos K).trans_le (hwf a')
  have hwlog := log_weight_bounds w hw hwf a'
  have hQ : IsDist (Qsel P v) ∧ (∀ a, wFloor K ≤ Qsel P v a) := by
    unfold Qsel
    split_ifs <;> exact ⟨by assumption, by assumption⟩
  have hQpos := (floor_pos K).trans_le (hQ.2 a')
  have hQlog := log_weight_bounds (Qsel P v) hQ.1 hQ.2 a'
  have hlogabs : |Real.log (Qsel P v a' / w a')| ≤ Real.log (nA K * (1 + beta K * K)) := by
    rw [Real.log_div hQpos.ne' hwpos.ne']
    apply abs_le.mpr
    constructor <;> linarith [hwlog.1, hwlog.2, hQlog.1, hQlog.2]
  have hp₁ := OneRoundTrade46.spread_mem hK a'
  have hp₂ := OneRoundTrade46.spread_mem hK P.1
  have profit_mem (a : Act K) : profit (pt K v) (pt K a.1) ∈ Set.Icc (0 : ℝ) 1 := by
    unfold profit tradeBit
    split_ifs <;> simpa using OneRoundTrade46.spread_mem hK a
  have hprofit : |profit (pt K v) (pt K a'.1) - profit (pt K v) (pt K P.1.1)| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [(profit_mem a').1, (profit_mem a').2, (profit_mem P.1).1, (profit_mem P.1).2]
  unfold hScore Hpar
  calc
    _ ≤ |profit (pt K v) (pt K a'.1) - profit (pt K v) (pt K P.1.1)| +
        |beta K * Real.log (Qsel P v a' / w a')| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg (beta_nonneg K)]
      exact add_le_add hprofit (mul_le_mul_of_nonneg_left hlogabs (beta_nonneg K))

end BilateralProfit.OneRoundSubmission46

namespace BilateralProfit.OneRoundSubmission46

variable {K : ℕ}

theorem feedback_sum (ρ : Grid K × Act K → ℝ) (a : Act K) (f : Bool → Act K → ℝ) :
    (∑ x, ρ x * (if Trades (pt K x.1) (pt K a.1) then f true x.2 else f false x.2)) =
      ∑ a', ∑ z : Bool, jointP ρ a a' z * f z a' := by
  classical
  have hrow (a' : Act K) :
      (∑ v : Grid K, ρ (v, a') * (if Trades (pt K v) (pt K a.1) then f true a' else f false a')) =
        ∑ z : Bool, jointP ρ a a' z * f z a' := by
    rw [Fintype.sum_bool]
    unfold jointP
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : Trades (pt K v) (pt K a.1) <;> simp [h]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun a' _ => hrow a')

theorem expected_score_eq (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ) (a : Act K) :
    expectedScore w ρ (proposal ρ a) = gap ρ a - beta K *
      ∑ a', ∑ z : Bool, jointP ρ a a' z * Real.log (update ρ a z a' / w a') := by
  classical
  have hpoint (x : Grid K × Act K) : ρ x * hScore w (proposal ρ a) x.1 x.2 =
      ρ x * (profit (pt K x.1) (pt K x.2.1) - profit (pt K x.1) (pt K a.1)) -
        beta K * (ρ x * (if Trades (pt K x.1) (pt K a.1) then
          Real.log (update ρ a true x.2 / w x.2) else Real.log (update ρ a false x.2 / w x.2))) := by
    unfold hScore proposal Qsel
    split_ifs <;> ring
  unfold expectedScore
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, feedback_sum ρ a (fun z a' => Real.log (update ρ a z a' / w a'))]
  rfl

theorem marginal_kl_nonneg (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (w : Act K → ℝ) (hw : IsDist w) (hwpos : ∀ a, 0 < w a) :
    0 ≤ ∑ a, margA ρ a * Real.log (margA ρ a / w a) := by
  have h := SinkhornHall.lemma_1_1 (margA ρ) w (OneRoundInfo46.marg_nonneg ρ hρ) hw.1
    ((OneRoundInfo46.marg_sum ρ hρ).trans hw.2.symm)
  have hnot : ¬∃ a, w a = 0 ∧ 0 < margA ρ a := by
    rintro ⟨a, ha, _⟩
    exact (hwpos a).ne' ha
  rw [SinkhornHall.klDiv, if_neg hnot, EReal.coe_le_coe_iff, OneRoundInfo46.marg_sum ρ hρ] at h
  exact (by positivity : (0 : ℝ) ≤ (∑ a, |margA ρ a - w a|) ^ 2 / (2 * 1)).trans h

noncomputable def mixFactor (K : ℕ) : ℝ := beta K * K / (1 + beta K * K)

theorem mixFactor_pos (hK : 0 < K) (hβ : 0 < beta K) : 0 < mixFactor K := by
  unfold mixFactor
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  positivity

theorem update_log_lower (hK : 0 < K) (hβ : 0 < beta K)
    (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (hρpos : ∀ x, 0 < ρ x)
    (w : Act K → ℝ) (hwpos : ∀ a, 0 < w a) (a a' : Act K) (z : Bool) :
    Real.log (jointP ρ a a' z / (margA ρ a' * zP ρ a z)) +
        Real.log (margA ρ a' / w a') + Real.log (mixFactor K) ≤
      Real.log (update ρ a z a' / w a') := by
  have hj := joint_pos hK ρ hρpos a a' z
  have hm := marg_pos hK ρ hρ hρpos a'
  have hz := z_pos hK ρ hρ hρpos a z
  have hMix := mixFactor_pos hK hβ
  have hw := hwpos a'
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hd : 0 < 1 + beta K * K := by positivity
  have hQ : mixFactor K * (jointP ρ a a' z / zP ρ a z) ≤ update ρ a z a' := by
    unfold mixFactor update
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hd.le
    have hA := nA_pos K
    have hnonneg : 0 ≤ 1 / nA K := by positivity
    linarith
  have hQratio := div_le_div_of_nonneg_right hQ hw.le
  have hratio : 0 < mixFactor K * (jointP ρ a a' z / zP ρ a z) / w a' := by positivity
  have hlog := Real.log_le_log hratio hQratio
  have hid : mixFactor K * (jointP ρ a a' z / zP ρ a z) / w a' =
      (jointP ρ a a' z / (margA ρ a' * zP ρ a z)) * (margA ρ a' / w a') * mixFactor K := by
    field_simp [hm.ne', hz.ne', hw.ne']
  have hI : 0 < jointP ρ a a' z / (margA ρ a' * zP ρ a z) := by positivity
  have hM : 0 < margA ρ a' / w a' := by positivity
  rw [hid, Real.log_mul (mul_ne_zero hI.ne' hM.ne') hMix.ne', Real.log_mul hI.ne' hM.ne'] at hlog
  exact hlog

theorem joint_weighted (ρ : Grid K × Act K → ℝ) (a : Act K) (g : Act K → ℝ) :
    (∑ a', ∑ z : Bool, jointP ρ a a' z * g a') = ∑ a', margA ρ a' * g a' := by
  apply Finset.sum_congr rfl
  intro a' _
  rw [← Finset.sum_mul, OneRoundInfo46.row_sum]

theorem joint_constant (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : Act K) (c : ℝ) :
    (∑ a', ∑ z : Bool, jointP ρ a a' z * c) = c := by
  rw [joint_weighted, ← Finset.sum_mul, OneRoundInfo46.marg_sum ρ hρ, one_mul]

theorem expected_log_lower (hK : 0 < K) (hβ : 0 < beta K)
    (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (hρpos : ∀ x, 0 < ρ x)
    (w : Act K → ℝ) (hw : IsDist w) (hwpos : ∀ a, 0 < w a) (a : Act K) :
    info ρ a + Real.log (mixFactor K) ≤
      ∑ a', ∑ z : Bool, jointP ρ a a' z * Real.log (update ρ a z a' / w a') := by
  have hpoint := Finset.sum_le_sum (fun a' (_ : a' ∈ Finset.univ) =>
    Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (update_log_lower hK hβ ρ hρ hρpos w hwpos a a' z)
        (OneRoundInfo46.joint_nonneg ρ hρ a a' z)))
  have heq : (∑ a', ∑ z : Bool, jointP ρ a a' z *
      (Real.log (jointP ρ a a' z / (margA ρ a' * zP ρ a z)) +
        Real.log (margA ρ a' / w a') + Real.log (mixFactor K))) =
      info ρ a + (∑ a', margA ρ a' * Real.log (margA ρ a' / w a')) + Real.log (mixFactor K) := by
    simp only [mul_add, Finset.sum_add_distrib, joint_weighted, joint_constant ρ hρ a]
    rfl
  rw [heq] at hpoint
  have hkl := marginal_kl_nonneg ρ hρ w hw hwpos
  linarith

theorem smoothing_penalty (hK : 0 < K) (hβ : 0 < beta K) :
    -(1 / (K : ℝ)) ≤ beta K * Real.log (mixFactor K) := by
  have hMix := mixFactor_pos hK hβ
  have h := Real.one_sub_inv_le_log_of_pos hMix
  have hm := mul_le_mul_of_nonneg_left h hβ.le
  have hKr : (K : ℝ) ≠ 0 := (Nat.cast_pos.mpr hK).ne'
  have heq : beta K * (1 - (mixFactor K)⁻¹) = -(1 / (K : ℝ)) := by
    unfold mixFactor
    field_simp [hβ.ne', hKr]
    ring
  rw [heq] at hm
  exact hm

theorem candidate_expected_bound (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (hρpos : ∀ x, 0 < ρ x) (w : Act K → ℝ) (hw : IsDist w)
    (hwf : ∀ a, wFloor K ≤ w a) (a : Act K) :
    expectedScore w ρ (proposal ρ a) ≤ gap ρ a - beta K * info ρ a + 1 / K := by
  rw [expected_score_eq]
  by_cases hβ0 : beta K = 0
  · simp only [hβ0, zero_mul, sub_zero]
    exact le_add_of_nonneg_right (by positivity)
  · have hβ : 0 < beta K := lt_of_le_of_ne (beta_nonneg K) (Ne.symm hβ0)
    have hlog := expected_log_lower hK hβ ρ hρ hρpos w hw
      (fun a => (floor_pos K).trans_le (hwf a)) a
    have hmul := mul_le_mul_of_nonneg_left hlog hβ.le
    have hpen := smoothing_penalty hK hβ
    nlinarith

end BilateralProfit.OneRoundSubmission46

namespace BilateralProfit.OneRoundSubmission46

open OneRoundProgram46 CapacitatedAssort.General

variable {K : ℕ}

theorem candidate_value (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ) (a : Act K) :
    Value (candidate K w ρ a) (update ρ a false, update ρ a true,
      expectedScore w ρ (proposal ρ a)) := by
  classical
  have hj (z : Bool) (a' : Act K) :
      (∑ v : Grid K, ρ (v,a') * (if z then tradeBit (pt K v) (pt K a.1)
        else 1 - tradeBit (pt K v) (pt K a.1))) = jointP ρ a a' z := by
    apply Finset.sum_congr rfl
    intro v _
    cases z <;> by_cases h : Trades (pt K v) (pt K a.1) <;> simp [tradeBit, jointP, h]
  have ht1 : Value (tab (actList K) fun a' => sumW (gridList K) fun v => do
      charge 6; pure (ρ (v,a') * tradeBit (pt K v) (pt K a.1))) (fun a' => jointP ρ a a' true) := by
    apply tab_value_total _ (mem_actList K)
    intro a' _
    have h := sumW_value (gridList K) (fun v => do charge 6; pure (ρ (v,a') * tradeBit (pt K v) (pt K a.1))) (fun v => ρ (v,a') * tradeBit (pt K v) (pt K a.1))
      (fun v _ => value_bind (value_charge 6) (value_pure _))
    simpa only [sum_gridList, ← hj true a', ↓reduceIte] using h
  have ht0 : Value (tab (actList K) fun a' => sumW (gridList K) fun v => do
      charge 7; pure (ρ (v,a') * (1 - tradeBit (pt K v) (pt K a.1)))) (fun a' => jointP ρ a a' false) := by
    apply tab_value_total _ (mem_actList K)
    intro a' _
    have h := sumW_value (gridList K) (fun v => do charge 7; pure (ρ (v,a') * (1-tradeBit (pt K v) (pt K a.1)))) (fun v => ρ (v,a') * (1-tradeBit (pt K v) (pt K a.1)))
      (fun v _ => value_bind (value_charge 7) (value_pure _))
    simpa only [sum_gridList, ← hj false a', Bool.false_eq_true, ↓reduceIte] using h
  unfold candidate
  apply value_bind ht1
  apply value_bind ht0
  apply value_bind (show Value (sumW (actList K) fun a' => do
      charge 1; pure (jointP ρ a a' true)) (zP ρ a true) from by
    simpa only [sum_actList, zP] using sumW_value (actList K) _ (fun a' => jointP ρ a a' true)
      (fun a' _ => value_bind (value_charge 1) (value_pure _)))
  apply value_bind (show Value (sumW (actList K) fun a' => do
      charge 1; pure (jointP ρ a a' false)) (zP ρ a false) from by
    simpa only [sum_actList, zP] using sumW_value (actList K) _ (fun a' => jointP ρ a a' false)
      (fun a' _ => value_bind (value_charge 1) (value_pure _)))
  apply value_bind (tab_value_total (actList K) (mem_actList K) _ (update ρ a true)
    (fun a' _ => value_bind (value_charge 9) (value_pure _)))
  apply value_bind (tab_value_total (actList K) (mem_actList K) _ (update ρ a false)
    (fun a' _ => value_bind (value_charge 9) (value_pure _)))
  apply value_bind (show Value (sumW (tableList K) fun x => do
      charge 20; pure (ρ x * hScore w (proposal ρ a) x.1 x.2))
      (expectedScore w ρ (proposal ρ a)) from by
    simpa only [sum_tableList, expectedScore] using sumW_value (tableList K) _
      (fun x => ρ x * hScore w (proposal ρ a) x.1 x.2)
      (fun x _ => value_bind (value_charge 20) (value_pure _)))
  exact value_pure _

noncomputable def selected (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ) : Proposal K × ℝ :=
  ((actList K).foldl (fun best a => OneRoundSelection46.pick
    (proposal ρ a, expectedScore w ρ (proposal ρ a)) best) none).getD (default,0)

noncomputable def nextTable (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ) : Grid K × Act K → ℝ :=
  fun x => ρ x * (1 + eta K * hScore w (selected w ρ).1 x.1 x.2) / (1+eta K*(selected w ρ).2)

theorem oneStep_value (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ) :
    Value (oneStep K w ρ) ((selected w ρ).1, nextTable w ρ) := by
  classical
  unfold oneStep
  have hloop := forIn_value (actList K) (fun a best => do
      charge 1
      let (Q0,Q1,sc) ← candidate K w ρ a
      match best with
      | none => pure (.yield (some ((a,Q0,Q1),sc)))
      | some (_,bsc) => do
        charge 1
        if sc < bsc then pure (.yield (some ((a,Q0,Q1),sc)))
        else pure (.yield best))
    (fun a best => OneRoundSelection46.pick (proposal ρ a, expectedScore w ρ (proposal ρ a)) best) (by
      intro a ha best
      apply value_bind (value_charge 1)
      apply value_bind (candidate_value w ρ a)
      cases best with
      | none => exact value_pure _
      | some b =>
        apply value_bind (value_charge 1)
        by_cases h : expectedScore w ρ (proposal ρ a) < b.2
        · simp only [h, ↓reduceIte, OneRoundSelection46.pick]
          exact value_pure _
        · simp only [h, ↓reduceIte, OneRoundSelection46.pick]
          exact value_pure _) none
  apply value_bind hloop
  apply value_bind (value_charge 1)
  apply value_bind (tab_value_total (tableList K) (mem_tableList K) _ (nextTable w ρ)
    (fun x _ => value_bind (value_charge 22) (value_pure _)))
  exact value_pure _

theorem selected_spec (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ) :
    ∃ a : Act K, selected w ρ = (proposal ρ a, expectedScore w ρ (proposal ρ a)) ∧
      ∀ b : Act K, (selected w ρ).2 ≤ expectedScore w ρ (proposal ρ b) := by
  have hl : actList K ≠ [] := by
    have h := mem_actList K (default : Act K)
    intro he
    simpa only [he, List.not_mem_nil] using h
  obtain ⟨a, ha, he, hmin⟩ := OneRoundSelection46.fold_pick_getD_min
    (fun a => (proposal ρ a, expectedScore w ρ (proposal ρ a))) (actList K) hl (default,0)
  refine ⟨a, he, ?_⟩
  intro b
  unfold selected
  rw [he]
  exact hmin b (mem_actList K b)

end BilateralProfit.OneRoundSubmission46

namespace BilateralProfit.OneRoundSubmission46

open OneRoundProgram46 CapacitatedAssort.General

variable {K : ℕ}

theorem selected_updates (hK : 0<K) (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ)
    (hρ : IsDist ρ) (hp : ∀ x, 0<ρ x) :
    IsDist (selected w ρ).1.2.1 ∧ IsDist (selected w ρ).1.2.2 ∧
      (∀ a, wFloor K ≤ (selected w ρ).1.2.1 a) ∧
      (∀ a, wFloor K ≤ (selected w ρ).1.2.2 a) := by
  obtain ⟨a, ha, _⟩ := selected_spec w ρ
  rw [ha]
  exact ⟨update_isDist hK ρ hρ hp a false, update_isDist hK ρ hρ hp a true,
    fun a' => update_floor ρ hρ a a' false, fun a' => update_floor ρ hρ a a' true⟩

theorem selected_score (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ) :
    (selected w ρ).2 = expectedScore w ρ (selected w ρ).1 := by
  obtain ⟨a, ha, _⟩ := selected_spec w ρ
  rw [ha]

theorem selected_score_abs (hK : 0<K) (w : Act K → ℝ) (hw : IsDist w)
    (hwf : ∀ a, wFloor K ≤ w a) (ρ : Grid K × Act K → ℝ)
    (hρ : IsDist ρ) (hp : ∀ x, 0<ρ x) (x : Grid K × Act K) :
    |hScore w (selected w ρ).1 x.1 x.2| ≤ Hpar K := by
  obtain ⟨h0,h1,hf0,hf1⟩ := selected_updates hK w ρ hρ hp
  exact score_abs_le hK w hw hwf _ h0 h1 hf0 hf1 _ _

theorem selected_mean_abs (hK : 0<K) (w : Act K → ℝ) (hw : IsDist w)
    (hwf : ∀ a, wFloor K ≤ w a) (ρ : Grid K × Act K → ℝ)
    (hρ : IsDist ρ) (hp : ∀ x, 0<ρ x) : |(selected w ρ).2| ≤ Hpar K := by
  rw [selected_score, expectedScore]
  calc
    _ ≤ ∑ x, |ρ x * hScore w (selected w ρ).1 x.1 x.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ρ x * Hpar K := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul, abs_of_nonneg (hρ.1 x)]
      exact mul_le_mul_of_nonneg_left (selected_score_abs hK w hw hwf ρ hρ hp x) (hρ.1 x)
    _ = _ := by rw [← Finset.sum_mul, hρ.2, one_mul]

theorem nextTable_invariant (hK : 0<K) (w : Act K → ℝ) (hw : IsDist w)
    (hwf : ∀ a, wFloor K ≤ w a) (ρ : Grid K × Act K → ℝ)
    (hρ : IsDist ρ) (hp : ∀ x, 0<ρ x) :
    IsDist (nextTable w ρ) ∧ ∀ x, 0<nextTable w ρ x := by
  have hη := eta_pos hK
  have hηH := eta_times_H_le_half hK
  have hnum (x : Grid K × Act K) : 0 < 1+eta K*hScore w (selected w ρ).1 x.1 x.2 := by
    have h := mul_le_mul_of_nonneg_left (abs_le.mp (selected_score_abs hK w hw hwf ρ hρ hp x)).1 hη.le
    nlinarith
  have hden : 0 < 1+eta K*(selected w ρ).2 := by
    have h := mul_le_mul_of_nonneg_left (abs_le.mp (selected_mean_abs hK w hw hwf ρ hρ hp)).1 hη.le
    nlinarith
  have hpos (x : Grid K × Act K) : 0 < nextTable w ρ x := by
    exact div_pos (mul_pos (hp x) (hnum x)) hden
  refine ⟨⟨fun x => (hpos x).le, ?_⟩, hpos⟩
  unfold nextTable
  rw [← Finset.sum_div]
  have heq : (∑ x, ρ x * (1+eta K*hScore w (selected w ρ).1 x.1 x.2)) =
      1+eta K*(selected w ρ).2 := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, hρ.2, selected_score, expectedScore]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq, div_self hden.ne']

theorem selected_mean_le (hK : 0<K) (C : ℝ)
    (hC : ∀ ρ : Grid K × Act K → ℝ, IsDist ρ → ∃ a : Act K,
      gap ρ a-beta K*info ρ a ≤ C/K)
    (w : Act K → ℝ) (hw : IsDist w) (hwf : ∀ a, wFloor K ≤ w a)
    (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (hp : ∀ x, 0<ρ x) :
    (selected w ρ).2 ≤ (C+1)/K := by
  obtain ⟨a, ha⟩ := hC ρ hρ
  obtain ⟨b, hb, hmin⟩ := selected_spec w ρ
  have hc := candidate_expected_bound hK ρ hρ hp w hw hwf a
  have hm := hmin a
  calc
    _ ≤ gap ρ a-beta K*info ρ a+1/K := hm.trans hc
    _ ≤ C/K+1/K := by linarith
    _ = _ := by ring

noncomputable def evolve (w : Act K → ℝ) : ℕ → (Grid K × Act K → ℝ) → (Grid K × Act K → ℝ)
  | 0, ρ => ρ
  | n+1, ρ => evolve w n (nextTable w ρ)

theorem evolve_succ (w : Act K → ℝ) (n : ℕ) (ρ : Grid K × Act K → ℝ) :
    evolve w (n+1) ρ = nextTable w (evolve w n ρ) := by
  induction n generalizing ρ with
  | zero => rfl
  | succ n ih => exact ih (nextTable w ρ)

noncomputable def tableAt (w : Act K → ℝ) (n : ℕ) : Grid K × Act K → ℝ :=
  evolve w n (fun _ => 1/(nA K*nG K))

noncomputable def proposalAt (w : Act K → ℝ) (n : ℕ) : Proposal K :=
  (selected w (tableAt w n)).1

theorem tableAt_invariant (hK : 0<K) (w : Act K → ℝ) (hw : IsDist w)
    (hwf : ∀ a, wFloor K ≤ w a) (n : ℕ) :
    IsDist (tableAt w n) ∧ ∀ x, 0<tableAt w n x := by
  have hden : 0<nA K*nG K := mul_pos (nA_pos K) (by rw [nG_eq]; positivity)
  induction n with
  | zero =>
    refine ⟨⟨fun _ => (one_div_pos.mpr hden).le, ?_⟩, fun _ => one_div_pos.mpr hden⟩
    change (∑ _x : Grid K × Act K, 1/(nA K*nG K)) = 1
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.card_univ, Fintype.card_prod, Nat.cast_mul]
    change nG K*nA K*(1/(nA K*nG K))=1
    rw [← div_eq_mul_one_div, mul_comm (nG K) (nA K), div_self hden.ne']
  | succ n ih =>
    change IsDist (evolve w (n+1) _) ∧ ∀ x, 0<evolve w (n+1) _ x
    rw [evolve_succ]
    exact nextTable_invariant hK w hw hwf _ ih.1 ih.2

theorem oneRoundLoop_value (w : Act K → ℝ) (n : ℕ) (ρ : Grid K × Act K → ℝ) :
    Value (oneRoundLoop K w n ρ) (selected w (evolve w n ρ)).1 := by
  induction n generalizing ρ with
  | zero => exact value_bind (oneStep_value w ρ) (value_pure _)
  | succ n ih => exact value_bind (oneStep_value w ρ) (ih (nextTable w ρ))

theorem oneRound_value_at (w : Act K → ℝ) (j : Fin (Jpar K)) :
    Value (oneRound K w j) (proposalAt w j.val) := by
  unfold oneRound
  apply value_bind (value_charge 40)
  apply value_bind (tab_value_total (tableList K) (mem_tableList K) _
    (fun _ => 1/(nA K*nG K)) (fun _ _ => value_bind (value_charge 3) (value_pure _)))
  exact oneRoundLoop_value w j.val _

theorem oneRoundVal_eq (w : Act K → ℝ) (j : Fin (Jpar K)) :
    oneRoundVal K w j = proposalAt w j.val := oneRound_value_at w j 0

theorem oneRound_value (w : Act K → ℝ) (j : Fin (Jpar K)) :
    Value (oneRound K w j) (oneRoundVal K w j) := by
  rw [oneRoundVal_eq]
  exact oneRound_value_at w j

theorem oneRound_updates (hK : 0<K) (w : Act K → ℝ) (hw : IsDist w)
    (hwf : ∀ a, wFloor K ≤ w a) (j : Fin (Jpar K)) :
    IsDist (oneRoundVal K w j).2.1 ∧ IsDist (oneRoundVal K w j).2.2 ∧
      (∀ a, wFloor K ≤ (oneRoundVal K w j).2.1 a) ∧
      (∀ a, wFloor K ≤ (oneRoundVal K w j).2.2 a) := by
  rw [oneRoundVal_eq]
  exact selected_updates hK w _ (tableAt_invariant hK w hw hwf j.val).1
    (tableAt_invariant hK w hw hwf j.val).2

end BilateralProfit.OneRoundSubmission46

namespace BilateralProfit.OneRoundSubmission46

open Finset

theorem normalized_mwu {X : Type} [Fintype X] [Nonempty X]
    (η H : ℝ) (hη : 0 < η) (hH : 0 < H) (hηH : η * H ≤ 1/2)
    (s : ℕ → X → ℝ) (hs : ∀ t x, |s t x| ≤ H)
    (ρ : ℕ → X → ℝ) (hρ : ∀ t, IsDist (ρ t))
    (hinit : ∀ x, ρ 0 x = 1 / Fintype.card X)
    (hrec : ∀ t x, ρ (t+1) x = ρ t x * (1+η*s t x) /
      (1+η*(∑ y, ρ t y*s t y))) (T : ℕ) (x : X) :
    (∑ t ∈ range T, s t x) ≤ (∑ t ∈ range T, ∑ y, ρ t y * s t y) +
      Real.log (Fintype.card X) / η + η * T * H ^ 2 := by
  classical
  let ℓ : ℕ → X → ℝ := fun t x => -s t x / H
  have hℓ : ∀ t x, ℓ t x ∈ Set.Icc (-1:ℝ) 1 := by
    intro t x
    have hh := abs_le.mp (hs t x)
    dsimp [ℓ]
    constructor
    · apply (le_div_iff₀ hH).mpr; nlinarith
    · apply (div_le_iff₀ hH).mpr; nlinarith
  have he (t : ℕ) : |∑ y, ρ t y*s t y| ≤ H := by
    calc
      _ ≤ ∑ y, |ρ t y*s t y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, ρ t y*H := by
        apply sum_le_sum
        intro y _
        rw [abs_mul, abs_of_nonneg ((hρ t).1 y)]
        exact mul_le_mul_of_nonneg_left (hs t y) ((hρ t).1 y)
      _ = H := by rw [← sum_mul, (hρ t).2, one_mul]
  have hd (t : ℕ) : 0 < 1+η*(∑ y, ρ t y*s t y) := by
    have := (abs_le.mp (he t)).1
    have := mul_le_mul_of_nonneg_left this hη.le
    nlinarith
  let c : ℕ → ℝ := fun t => (Fintype.card X : ℝ) *
    ∏ k ∈ range t, (1+η*(∑ y, ρ k y*s k y))
  have hcpos (t : ℕ) : 0 < c t := by
    dsimp [c]
    apply mul_pos (by exact_mod_cast Fintype.card_pos)
    exact prod_pos (fun k _ => hd k)
  have hcsucc (t : ℕ) : c (t+1) = c t * (1+η*(∑ y, ρ t y*s t y)) := by
    simp [c, prod_range_succ, mul_assoc]
  have hw (t : ℕ) (y : X) : mwWeight (η*H) ℓ t y = c t * ρ t y := by
    induction t with
    | zero => simp [mwWeight, c, hinit, (show (Fintype.card X : ℝ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero)]
    | succ t ih =>
      change mwWeight (η*H) ℓ t y * (1-η*H*ℓ t y) = _
      rw [ih, hcsucc, hrec]
      dsimp [ℓ]
      field_simp [hH.ne', (hd t).ne']
      <;> ring
  have hp (t : ℕ) (y : X) : mwDist (η*H) ℓ t y = ρ t y := by
    unfold mwDist
    simp_rw [hw]
    rw [← mul_sum, (hρ t).2, mul_one]
    exact mul_div_cancel_left₀ _ (hcpos t).ne'
  have hbound := proposition_4_7 (η*H) (mul_pos hη hH) hηH T ℓ hℓ x
  have hsabs : (∑ t ∈ range T, |ℓ t x|) ≤ T := by
    calc
      _ ≤ ∑ _t ∈ range T, (1:ℝ) := by
        apply sum_le_sum
        intro t _
        exact (abs_le.mpr (hℓ t x))
      _ = _ := by simp
  have hbound' : (∑ t ∈ range T, ∑ i, mwDist (η*H) ℓ t i * ℓ t i) ≤
      (∑ t ∈ range T, ℓ t x) + (η*H)*T + Real.log (Fintype.card X)/(η*H) := by
    have := mul_le_mul_of_nonneg_left hsabs (mul_pos hη hH).le
    linarith
  have ha : (∑ t ∈ range T, ∑ i, mwDist (η*H) ℓ t i * ℓ t i) =
      -(∑ t ∈ range T, ∑ i, ρ t i*s t i)/H := by
    simp_rw [hp]
    dsimp [ℓ]
    simp only [← mul_div_assoc, mul_neg, ← sum_div, ← sum_neg_distrib]
  have hb : (∑ t ∈ range T, ℓ t x) = -(∑ t ∈ range T, s t x)/H := by
    dsimp [ℓ]
    rw [← sum_div, ← sum_neg_distrib]
  rw [ha, hb] at hbound'
  have hh := mul_le_mul_of_nonneg_right hbound' hH.le
  field_simp [hH.ne', hη.ne'] at hh ⊢
  nlinarith

end BilateralProfit.OneRoundSubmission46

namespace BilateralProfit

open OneRoundSubmission46 Finset

theorem cert_lemma_4_6_submission (K : ℕ) (hK : 0 < K) (C₀ : ℝ)
    (hC₀ : ∀ ρ : Grid K × Act K → ℝ, IsDist ρ →
      ∃ a : Act K, gap ρ a - beta K * info ρ a ≤ C₀ / K)
    (w : Act K → ℝ) (hw : IsDist w) (hwf : ∀ a', wFloor K ≤ w a')
    (v : Grid K) (a' : Act K) :
    (∑ j : Fin (Jpar K), hScore w (oneRoundVal K w j) v a') / Jpar K ≤ (C₀ + 2) / K := by
  classical
  have hinv := tableAt_invariant hK w hw hwf
  let s : ℕ → Grid K × Act K → ℝ := fun t x => hScore w (proposalAt w t) x.1 x.2
  have hs (t : ℕ) (x : Grid K × Act K) : |s t x| ≤ Hpar K :=
    selected_score_abs hK w hw hwf _ (hinv t).1 (hinv t).2 x
  have hrec (t : ℕ) (x : Grid K × Act K) :
      tableAt w (t+1) x = tableAt w t x * (1+eta K*s t x) /
        (1+eta K*(∑ y, tableAt w t y*s t y)) := by
    change evolve w (t+1) _ x = _
    rw [evolve_succ]
    change nextTable w (tableAt w t) x = _
    unfold nextTable
    rw [selected_score]
    rfl
  have hinit (x : Grid K × Act K) : tableAt w 0 x = 1 / Fintype.card (Grid K × Act K) := by
    change 1/(nA K*nG K) = _
    rw [Fintype.card_prod, Nat.cast_mul]
    change 1/(nA K*nG K)=1/(nG K*nA K)
    rw [mul_comm (nA K)]
  have hmwu := normalized_mwu (eta K) (Hpar K) (eta_pos hK) (H_pos K)
    (eta_times_H_le_half hK) s hs (tableAt w) (fun t => (hinv t).1)
    hinit hrec (Jpar K) (v,a')
  have hlog : Real.log (Fintype.card (Grid K × Act K)) = Real.log (nA K*nG K) := by
    rw [Fintype.card_prod, Nat.cast_mul]
    change Real.log (nG K*nA K) = _
    rw [mul_comm]
  rw [hlog] at hmwu
  have he (t : ℕ) : (∑ y, tableAt w t y*s t y) ≤ (C₀+1)/K := by
    change expectedScore w (tableAt w t) (selected w (tableAt w t)).1 ≤ _
    rw [← selected_score]
    exact selected_mean_le hK C₀ hC₀ w hw hwf _ (hinv t).1 (hinv t).2
  have hesum : (∑ t ∈ range (Jpar K), ∑ y, tableAt w t y*s t y) ≤
      (Jpar K : ℝ)*((C₀+1)/K) := by
    calc
      _ ≤ ∑ _t ∈ range (Jpar K), (C₀+1)/(K:ℝ) := sum_le_sum (fun t _ => he t)
      _ = _ := by simp
  have hJ : (0:ℝ)<Jpar K := Nat.cast_pos.mpr (J_pos hK)
  have hbudget := mul_le_mul_of_nonneg_left (regret_budget hK) hJ.le
  have heq : (Jpar K : ℝ)*(Real.log (nA K*nG K)/(eta K*Jpar K)+eta K*Hpar K^2) =
      Real.log (nA K*nG K)/eta K+eta K*Jpar K*Hpar K^2 := by
    field_simp [hJ.ne', (eta_pos hK).ne']
  rw [heq] at hbudget
  have htotal : (∑ t ∈ range (Jpar K), s t (v,a')) ≤
      (Jpar K : ℝ)*((C₀+2)/K) := by
    have heq' : (Jpar K : ℝ)*((C₀+1)/K)+(Jpar K : ℝ)*(1/K) =
        (Jpar K : ℝ)*((C₀+2)/K) := by ring
    linarith
  apply (div_le_iff₀ hJ).mpr
  have hsum : (∑ j : Fin (Jpar K), hScore w (oneRoundVal K w j) v a') =
      ∑ t ∈ range (Jpar K), s t (v,a') := by
    simp_rw [oneRoundVal_eq]
    exact Fin.sum_univ_eq_sum_range (fun t => hScore w (proposalAt w t) v a') (Jpar K)
  rw [hsum, mul_comm ((C₀+2)/(K:ℝ))]
  exact htotal

end BilateralProfit
open BilateralProfit

theorem solution (K : ℕ) (hK : 0 < K) (C₀ : ℝ)
    (hC₀ : ∀ ρ : Grid K × Act K → ℝ, IsDist ρ →
      ∃ a : Act K, gap ρ a - beta K * info ρ a ≤ C₀ / K)
    (w : Act K → ℝ) (hw : IsDist w) (hwf : ∀ a', wFloor K ≤ w a') (v : Grid K) (a' : Act K) :
    (∑ j : Fin (Jpar K), hScore w (oneRoundVal K w j) v a') / Jpar K ≤ (C₀ + 2) / K := by exact BilateralProfit.cert_lemma_4_6_submission K hK C₀ hC₀ w hw hwf v a'

