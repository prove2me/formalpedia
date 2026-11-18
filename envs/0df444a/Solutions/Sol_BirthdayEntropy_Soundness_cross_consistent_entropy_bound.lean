-- Prove2me | solution 1 for BirthdayEntropy.Soundness.cross_consistent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T01:03:56.368977+00:00
-- url     : https://prove2.me/submissions/7d3eb177-df02-4311-a27b-8dae767c233d

import Definitions.Def_BirthdayEntropy_Soundness_Counting
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Theorems.Thm_OAI_ThorpCompatibility_Law_condEntropy_eq_mean
import Theorems.Thm_OAI_ThorpCompatibility_Law_condEntropy_le_prediction
import Definitions.Def_BirthdayEntropy_Soundness_Biclique
import Theorems.Thm_OAI_ThorpCompatibility_Law_gibbs_le

noncomputable section
open scoped Classical
open Finset OAI.ThorpCompatibility
namespace BirthdayEntropy.Soundness.Info
variable {α β γ δ η : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype η]

lemma mean_map (P : Law α) (f : α → β) (g : β → ℝ) :
    (P.map f).mean g = P.mean (fun a => g (f a)) := by
  classical
  simp only [Law.mean, Law.map, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

lemma mean_congr_support (P : Law α) {f g : α → ℝ}
    (h : ∀ a, 0 < P.mass a → f a = g a) : P.mean f = P.mean g := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : P.mass a = 0
  · simp [ha]
  · rw [h a (lt_of_le_of_ne (P.nonneg a) (Ne.symm ha))]

lemma mass_le_map (P : Law α) (f : α → β) (a : α) : P.mass a ≤ (P.map f).mass (f a) := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun b => if f b = f a then P.mass b else 0)
    (fun b _ => by split_ifs <;> simp_all [P.nonneg]) (Finset.mem_univ a)
  simpa [Law.map] using h

lemma map_mass_pos (P : Law α) (f : α → β) {a : α} (ha : 0 < P.mass a) :
    0 < (P.map f).mass (f a) := lt_of_lt_of_le ha (mass_le_map P f a)

lemma entropy_fibers (P : Law α) (X : α → β) (Y : α → γ)
    (h : ∀ a b, X a = X b ↔ Y a = Y b) : (P.map X).entropy = (P.map Y).entropy := by
  rw [Law.entropy, Law.entropy, mean_map, mean_map]
  congr 1
  apply congrArg
  funext a
  congr 1
  simp only [Law.map]
  apply Finset.sum_congr rfl
  intro b _
  rw [h b a]

lemma mean_sub (P : Law α) (f g : α → ℝ) :
    P.mean (fun a => f a - g a) = P.mean f - P.mean g := by
  simp [Law.mean, mul_sub, Finset.sum_sub_distrib]

lemma mean_mono (P : Law α) {f g : α → ℝ}
    (h : ∀ a, 0 < P.mass a → f a ≤ g a) : P.mean f ≤ P.mean g := by
  apply Finset.sum_le_sum
  intro a ha
  by_cases hp : 0 < P.mass a
  · exact mul_le_mul_of_nonneg_left (h a hp) (P.nonneg a)
  · have hz : P.mass a = 0 := le_antisymm (le_of_not_gt hp) (P.nonneg a)
    simp [hz]

lemma mean_const (P : Law α) (c : ℝ) : P.mean (fun _ => c) = c := by
  simp [Law.mean,← Finset.sum_mul,P.total]

lemma mean_add (P : Law α) (f g : α → ℝ) :
    P.mean (fun a => f a + g a) = P.mean f + P.mean g := by
  simp [Law.mean,mul_add,Finset.sum_add_distrib]

lemma mean_mul (P : Law α) (c : ℝ) (f : α → ℝ) :
    P.mean (fun a => c * f a) = c * P.mean f := by
  simp only [Law.mean,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma predict_mass (P : Law α) (X : α → β) (Y : α → γ) {a : α} (ha : 0 < P.mass a) :
    (P.predict X Y (Y a)).mass (X a) = P.condMass X Y a := by
  have hp : 0 < P.prob (fun b => Y b = Y a) := by
    change 0 < ∑ b, if Y b = Y a then P.mass b else 0
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun b => if Y b = Y a then P.mass b else 0)
      (fun b _ => by split_ifs <;> simp_all [P.nonneg]) (Finset.mem_univ a)
    simp only [ite_true] at h
    exact ha.trans_le h
  have heq : P.prob (fun b => Y b = Y a) = (P.map Y).mass (Y a) := by
    simp [Law.prob, Law.map, mul_ite]
  unfold Law.predict Law.restrict
  rw [dif_pos hp]
  dsimp [Law.map, Law.condMass]
  simp only [Law.map] at heq
  rw [← heq, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp_all

lemma condEntropy_condition (P : Law α) (X : α → β) (Y : α → γ) (Z : α → δ) :
    P.condEntropy X (fun a => (Y a,Z a)) ≤ P.condEntropy X Y := by
  have hs : ∀ a, 0 < P.mass a → 0 < (P.predict X Y (Y a)).mass (X a) := by
    intro a ha
    rw [predict_mass P X Y ha]
    exact div_pos (map_mass_pos P _ ha) (map_mass_pos P _ ha)
  have h := P.condEntropy_le_prediction X (fun a => (Y a,Z a))
    (fun yz => P.predict X Y yz.1) hs
  rw [P.condEntropy_eq_mean X Y]
  apply le_trans h
  apply le_of_eq
  congr 1
  apply mean_congr_support
  intro a ha
  rw [predict_mass P X Y ha]

lemma mutualInfo_nonneg (P : Law α) (X : α → β) (Y : α → γ) :
    0 ≤ mutualInfo P X Y := by
  have hs : ∀ a, 0 < P.mass a → 0 < (P.map X).mass (X a) := fun a ha => map_mass_pos P X ha
  have h := P.condEntropy_le_prediction X Y (fun _ => P.map X) hs
  rw [← mean_map P X (fun x => Real.log ((P.map X).mass x))] at h
  change (P.map (fun a => (X a,Y a))).entropy - (P.map Y).entropy ≤ (P.map X).entropy at h
  unfold mutualInfo
  linarith

lemma mutualInfo_left (P : Law α) (X : α → β) (Y : α → γ) (f : β → δ) :
    mutualInfo P (fun a => f (X a)) Y ≤ mutualInfo P X Y := by
  have h := condEntropy_condition P X (fun a => f (X a)) Y
  unfold Law.condEntropy at h
  have h1 : (P.map (fun a => (X a, f (X a)))).entropy = (P.map X).entropy := by
    apply entropy_fibers
    intro a b
    simp only [Prod.mk.injEq]
    exact ⟨And.left, fun h => ⟨h, congrArg f h⟩⟩
  have h2 : (P.map (fun a => (X a, (f (X a),Y a)))).entropy = (P.map (fun a => (X a,Y a))).entropy := by
    apply entropy_fibers
    intro a b
    simp only [Prod.mk.injEq]
    constructor
    · exact fun h => ⟨h.1,h.2.2⟩
    · exact fun h => ⟨h.1,congrArg f h.1,h.2⟩
  rw [h1,h2] at h
  unfold mutualInfo
  linarith

lemma mutualInfo_symm (P : Law α) (X : α → β) (Y : α → γ) :
    mutualInfo P X Y = mutualInfo P Y X := by
  have h : (P.map (fun a => (X a,Y a))).entropy = (P.map (fun a => (Y a,X a))).entropy := by
    apply entropy_fibers
    intro a b
    simp [and_comm]
  unfold mutualInfo
  rw [h]
  ring

lemma mutualInfo_process (P : Law α) (X : α → β) (Y : α → γ) (f : β → δ) (g : γ → η) :
    mutualInfo P (fun a => f (X a)) (fun a => g (Y a)) ≤ mutualInfo P X Y := by
  calc
    _ ≤ mutualInfo P X (fun a => g (Y a)) := mutualInfo_left P X _ f
    _ = mutualInfo P (fun a => g (Y a)) X := mutualInfo_symm _ _ _
    _ ≤ mutualInfo P Y X := mutualInfo_left P Y X g
    _ = mutualInfo P X Y := mutualInfo_symm _ _ _
end BirthdayEntropy.Soundness.Info

noncomputable section
open scoped Classical
open Finset BirthdayEntropy.Soundness OAI.ThorpCompatibility
namespace BirthdayEntropy.Soundness.Code

abbrev State := Bool × Bool

def mask {n : ℕ} (A : Finset (Signed n)) (i : Fin n) : State :=
  (decide ((i,false) ∈ A),decide ((i,true) ∈ A))

def unmask {n : ℕ} (a : Fin n → State) : Finset (Signed n) :=
  Finset.univ.filter (fun p => if p.2 then (a p.1).2 else (a p.1).1)

lemma unmask_mask {n : ℕ} (A : Finset (Signed n)) : unmask (mask A) = A := by
  ext ⟨i,b⟩
  cases b <;> simp [unmask,mask]

lemma mask_unmask {n : ℕ} (a : Fin n → State) : mask (unmask a) = a := by
  funext i
  simp [mask,unmask]

def maskEquiv (n : ℕ) : Finset (Signed n) ≃ (Fin n → State) where
  toFun := mask
  invFun := unmask
  left_inv := unmask_mask
  right_inv := mask_unmask

def cross (a b : State) : Prop := ¬(a.1 = true ∧ b.2 = true) ∧ ¬(a.2 = true ∧ b.1 = true)

def bad (a : State) : Prop := a.1 = true ∧ a.2 = true

def terr (a b : State) : Prop := ¬bad a ∧ ¬bad b ∧
    ¬((a.1 = true ∧ b.1 = true) ∨ (a.2 = true ∧ b.2 = true))

def cost (x : ℝ) (a b : State) : ℝ := (if terr a b then 1 else 0) + x * (if bad a then 1 else 0)

def weight (x lam : ℝ) (b a : State) : ℝ :=
  match b with
  | (false,false) => if a = (true,true) then Real.exp (-lam*x) else Real.exp (-lam)
  | (true,false) => if a = (false,false) then Real.exp (-lam) else if a = (true,false) then 1 else 0
  | (false,true) => if a = (false,false) then Real.exp (-lam) else if a = (false,true) then 1 else 0
  | (true,true) => if a = (false,false) then 1 else 0

lemma weight_nonneg (x lam : ℝ) (b a : State) : 0 ≤ weight x lam b a := by
  rcases a with ⟨a₀,a₁⟩
  rcases b with ⟨b₀,b₁⟩
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;> simp [weight, Real.exp_nonneg]

lemma weight_empty_pos (x lam : ℝ) (b : State) : 0 < weight x lam b (false,false) := by
  rcases b with ⟨b₀,b₁⟩
  cases b₀ <;> cases b₁ <;> simp [weight,Real.exp_pos]

lemma weight_cross (x lam : ℝ) (a b : State) (h : cross a b) :
    weight x lam b a = Real.exp (-lam * cost x a b) := by
  rcases a with ⟨a₀,a₁⟩
  rcases b with ⟨b₀,b₁⟩
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;>
    simp_all [cross,weight,cost,terr,bad]

lemma cross_mask {n : ℕ} (F : Flattening n) (h : CrossConsistent F) (i : Fin n) :
    cross (mask F.1 i) (mask F.2 i) := by
  constructor
  · intro h'
    have h0 : (i,false) ∈ F.1 := by simpa [mask] using h'.1
    have h1 : (i,true) ∈ F.2 := by simpa [mask] using h'.2
    exact h i false h0 h1
  · intro h'
    have h1 : (i,true) ∈ F.1 := by simpa [mask] using h'.1
    have h0 : (i,false) ∈ F.2 := by simpa [mask] using h'.2
    exact h i true h1 h0

lemma bad_mask {n : ℕ} (A : Finset (Signed n)) (B : Finset (Signed n)) (i : Fin n) :
    bad (mask A i) ↔ i ∈ badLeft (A,B) := by simp [bad,mask,badLeft]

lemma terr_mask {n : ℕ} (F : Flattening n) (i : Fin n) :
    terr (mask F.1 i) (mask F.2 i) ↔ i ∈ terrible F := by
  simp [terr,bad,mask,terrible,badLeft,badRight,good,Bool.exists_bool,and_assoc,not_or]

lemma sum_cost {n : ℕ} (x : ℝ) (F : Flattening n) :
    (∑ i, cost x (mask F.1 i) (mask F.2 i)) =
      ((terrible F).card : ℝ) + x * (badLeft F).card := by
  simp only [cost,Finset.sum_add_distrib,← Finset.mul_sum]
  congr 1
  · simp_rw [terr_mask]
    simp
  · simp_rw [bad_mask F.1 F.2]
    simp

lemma total_weight_cross {n : ℕ} (x lam : ℝ) (F : Flattening n) (h : CrossConsistent F) :
    (∏ i, weight x lam (mask F.2 i) (mask F.1 i)) =
      Real.exp (-lam * (((terrible F).card : ℝ) + x * (badLeft F).card)) := by
  simp_rw [weight_cross x lam _ _ (cross_mask F h _)]
  rw [← Real.exp_sum, ← Finset.mul_sum, sum_cost]

lemma local_partition (x : ℝ) (hx : 0 < x) (hxhalf : x ≤ 1/2) (b : State) :
    (∑ a : State, weight x (4*Real.log (Real.exp 1/x)) b a) ≤ Real.exp x := by
  let A := Real.log (Real.exp 1/x)
  have hAeq : A = 1 - Real.log x := by
    dsimp [A]
    rw [Real.log_div (Real.exp_ne_zero _) hx.ne',Real.log_exp]
  have hA : 1 ≤ A := by
    have := Real.log_nonpos hx.le (show x ≤ 1 by linarith)
    linarith
  have he4 : Real.exp (-(4*A)) ≤ x^4 := by
    calc
      _ ≤ Real.exp ((4:ℝ)*Real.log x) := Real.exp_le_exp.mpr (by linarith)
      _ = x^4 := by rw [show (4:ℝ) = (4:ℕ) by norm_num, Real.exp_nat_mul,Real.exp_log hx]
  have he : 3 * Real.exp (-(4*A)) ≤ x := by
    have hx2 : x*x ≤ x/2 := by nlinarith
    have hx3 : x^4 ≤ x/8 := by
      nlinarith [mul_nonneg (show 0 ≤ x*x by positivity) (show 0 ≤ 1/4-x*x by nlinarith)]
    linarith
  have hex : Real.exp (-(4*A)*x) ≤ 1-x := by
    have hax : 4*x ≤ 4*A*x := by nlinarith
    have hlow := Real.add_one_le_exp (4*x)
    have hprod : (1-x)*(1+4*x) ≥ 1 := by nlinarith
    have hpos : 0 ≤ 1-x := by linarith
    have hp : 1 ≤ (1-x)*Real.exp (4*x) := by nlinarith
    rw [show -(4*A)*x = -(4*A*x) by ring]
    calc
      _ ≤ Real.exp (-(4*x)) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / Real.exp (4*x) := by rw [Real.exp_neg,one_div]
      _ ≤ 1-x := (div_le_iff₀ (Real.exp_pos _)).mpr hp
  have hexp : 1 ≤ Real.exp x := Real.one_le_exp hx.le
  have hxexp := Real.add_one_le_exp x
  change (∑ a : State, weight x (4*A) b a) ≤ Real.exp x
  simp only [neg_mul] at hex
  rcases b with ⟨b₀,b₁⟩
  cases b₀ <;> cases b₁ <;>
    simp [Fintype.sum_prod_type,Fintype.sum_bool,weight] <;> linarith [Real.exp_pos (-(4*A))]

lemma partition_pos {n : ℕ} (x lam : ℝ) (B : Finset (Signed n)) :
    0 < ∑ A : Finset (Signed n), ∏ i, weight x lam (mask B i) (mask A i) := by
  have hpos : 0 < ∏ i, weight x lam (mask B i) (mask (∅ : Finset (Signed n)) i) := by
    apply Finset.prod_pos
    intro i hi
    simpa [mask] using weight_empty_pos x lam (mask B i)
  exact hpos.trans_le (Finset.single_le_sum (f := fun A : Finset (Signed n) => ∏ i, weight x lam (mask B i) (mask A i)) (fun A _ => Finset.prod_nonneg (fun i _ => weight_nonneg x lam _ _)) (Finset.mem_univ ∅))

lemma partition_bound {n : ℕ} (x : ℝ) (hx : 0 < x) (hxhalf : x ≤ 1/2) (B : Finset (Signed n)) :
    (∑ A : Finset (Signed n), ∏ i, weight x (4*Real.log (Real.exp 1/x)) (mask B i) (mask A i)) ≤
      Real.exp ((n : ℝ)*x) := by
  have heq : (∑ A : Finset (Signed n), ∏ i, weight x (4*Real.log (Real.exp 1/x)) (mask B i) (mask A i)) =
      ∏ i, ∑ a : State, weight x (4*Real.log (Real.exp 1/x)) (mask B i) a := by
    rw [Fintype.prod_sum]
    exact (Equiv.sum_comp (maskEquiv n) (fun a => ∏ i, weight x (4*Real.log (Real.exp 1/x)) (mask B i) (a i)))
  rw [heq]
  calc
    _ ≤ ∏ _i : Fin n, Real.exp x := by
      apply Finset.prod_le_prod
      · intro i hi
        exact Finset.sum_nonneg (fun a _ => weight_nonneg _ _ _ _)
      · intro i hi
        exact local_partition x hx hxhalf _
    _ = Real.exp ((n : ℝ)*x) := by simp [← Real.exp_nat_mul]


def kernel {n : ℕ} (x : ℝ) (B : Finset (Signed n)) : Law (Finset (Signed n)) :=
  Law.tilt (fun A => ∏ i, weight x (4*Real.log (Real.exp 1/x)) (mask B i) (mask A i))
    (fun A => Finset.prod_nonneg (fun i _ => weight_nonneg _ _ _ _)) (partition_pos _ _ B)

lemma kernel_log {n : ℕ} (x : ℝ) (hx : 0 < x) (hxhalf : x ≤ 1/2)
    (F : Flattening n) (h : CrossConsistent F) :
    -(Real.log ((kernel x F.2).mass F.1)) ≤
      4*Real.log (Real.exp 1/x) * (((terrible F).card : ℝ) + x * (badLeft F).card) + n*x := by
  have hw : 0 < ∏ i, weight x (4*Real.log (Real.exp 1/x)) (mask F.2 i) (mask F.1 i) := by
    rw [total_weight_cross x _ F h]
    exact Real.exp_pos _
  change -Real.log ((∏ i, weight x (4*Real.log (Real.exp 1/x)) (mask F.2 i) (mask F.1 i)) /
    (∑ A, ∏ i, weight x (4*Real.log (Real.exp 1/x)) (mask F.2 i) (mask A i))) ≤ _
  rw [Real.log_div hw.ne' (partition_pos _ _ _).ne', total_weight_cross x _ F h,Real.log_exp]
  have hz := Real.log_le_log (partition_pos x (4*Real.log (Real.exp 1/x)) F.2)
      (partition_bound x hx hxhalf F.2)
  rw [Real.log_exp] at hz
  linarith

lemma conditional_code {α : Type*} [Fintype α] {n : ℕ} (P : Law α)
    (A B : α → Finset (Signed n)) (x : ℝ) (hx : 0 < x) (hxhalf : x ≤ 1/2)
    (hcross : ∀ z, 0 < P.mass z → CrossConsistent (A z,B z)) :
    P.condEntropy A B ≤ P.mean (fun z =>
      4*Real.log (Real.exp 1/x) * (((terrible (A z,B z)).card : ℝ) + x * (badLeft (A z,B z)).card)) + n*x := by
  have hs : ∀ z, 0 < P.mass z → 0 < (kernel x (B z)).mass (A z) := by
    intro z hz
    change 0 < (∏ i, weight x (4*Real.log (Real.exp 1/x)) (mask (B z) i) (mask (A z) i)) /
      (∑ T, ∏ i, weight x (4*Real.log (Real.exp 1/x)) (mask (B z) i) (mask T i))
    apply div_pos _ (partition_pos _ _ _)
    rw [total_weight_cross x _ (A z,B z) (hcross z hz)]
    exact Real.exp_pos _
  have h := P.condEntropy_le_prediction A B (kernel x) hs
  have hm := Info.mean_mono P (fun z hz => kernel_log x hx hxhalf (A z,B z) (hcross z hz))
  rw [Info.mean_add,Info.mean_const] at hm
  have hneg : -P.mean (fun z => Real.log ((kernel x (B z)).mass (A z))) =
      P.mean (fun z => -Real.log ((kernel x (B z)).mass (A z))) := by simp [Law.mean,Finset.sum_neg_distrib]
  rw [hneg] at h
  exact h.trans hm
end BirthdayEntropy.Soundness.Code

noncomputable section
open scoped Classical
open Finset OAI.ThorpCompatibility BirthdayEntropy.Soundness
namespace BirthdayEntropy.Soundness.Code

lemma terrible_swap {n : ℕ} (F : Flattening n) : terrible (F.2,F.1) = terrible F := by
  ext i
  simp [terrible,badLeft,badRight,good,Bool.exists_bool]
  tauto

lemma badCount_swap {n : ℕ} (F : Flattening n) : badCount (F.2,F.1) = badCount F := by
  simp [badCount,badRight,Nat.add_comm]

lemma energy_swap {n : ℕ} (ℓ : ℕ) (β : ℝ) (F : Flattening n) :
    energy ℓ β (F.2,F.1) = energy ℓ β F := by simp [energy,terrible_swap,badCount_swap]

lemma cross_swap {n : ℕ} (F : Flattening n) (h : CrossConsistent F) : CrossConsistent (F.2,F.1) := by
  intro i b hi hj
  have hh := h i (!b) hj
  apply hh
  simpa using hi

lemma cost_energy {n ℓ : ℕ} (β : ℝ) (F : Flattening n) (hx : 0 ≤ ratio n ℓ) :
    ((terrible F).card : ℝ) + ratio n ℓ * (badLeft F).card ≤ 2 * energy ℓ β F := by
  have ht : ((terrible F).card : ℝ) ≤ energy ℓ β F := le_max_left _ _
  have hb : ratio n ℓ * (badCount F : ℝ) ≤ energy ℓ β F := (le_max_left _ _).trans (le_max_right _ _)
  have hbc : ((badLeft F).card : ℝ) ≤ badCount F := by simp [badCount]
  nlinarith [mul_le_mul_of_nonneg_left hbc hx]

lemma energy_floor {n ℓ : ℕ} (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hx : 0 ≤ ratio n ℓ) (hx1 : ratio n ℓ ≤ 1) (F : Flattening n) :
    β * n * ratio n ℓ ≤ energy ℓ β F := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  unfold energy
  by_cases ht : ((terrible F).card : ℝ) < β * n
  · by_cases hb : (badCount F : ℝ) < β * n
    · rw [if_pos ⟨ht,hb⟩]
      apply le_trans _ (le_trans (le_max_right _ _) (le_max_right _ _))
      nlinarith [mul_nonneg hn hx]
    · apply le_trans _ (le_trans (le_max_left _ _) (le_max_right _ _))
      nlinarith [mul_le_mul_of_nonneg_left (le_of_not_gt hb) hx]
  · apply le_trans _ (le_max_left _ _)
    nlinarith [mul_le_mul_of_nonneg_left hx1 (mul_nonneg hβ.le hn), le_of_not_gt ht]

lemma generic_flatten_entropy {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    {n ℓ : ℕ} (P : Law α) (X : α → β) (Y : α → γ)
    (f : β → Finset (Signed n)) (g : γ → Finset (Signed n))
    (β₀ : ℝ) (hβ : 0 < β₀) (hβ1 : β₀ ≤ 1)
    (hx : 0 < ratio n ℓ) (hxhalf : ratio n ℓ ≤ 1/2)
    (hcross : ∀ z, 0 < P.mass z → CrossConsistent (f (X z),g (Y z))) :
    (P.map (fun z => (f (X z),g (Y z)))).entropy ≤ mutualInfo P X Y +
      (16+2/β₀)*logScale n ℓ * P.mean (fun z => energy ℓ β₀ (f (X z),g (Y z))) := by
  let A := fun z => f (X z)
  let B := fun z => g (Y z)
  let E := P.mean (fun z => energy ℓ β₀ (A z,B z))
  have hA1 : 1 ≤ logScale n ℓ := by
    unfold logScale
    have hle : Real.exp 1 ≤ Real.exp 1 / ratio n ℓ := (le_div_iff₀ hx).mpr (by nlinarith [Real.exp_pos 1])
    simpa using Real.log_le_log (Real.exp_pos 1) hle
  have hA : 0 < logScale n ℓ := by linarith
  have hcL := conditional_code P A B (ratio n ℓ) hx hxhalf hcross
  have hcR := conditional_code P B A (ratio n ℓ) hx hxhalf (fun z hz => cross_swap _ (hcross z hz))
  have hboundL : P.mean (fun z => 4*logScale n ℓ *
      (((terrible (A z,B z)).card : ℝ) + ratio n ℓ * (badLeft (A z,B z)).card)) ≤ 8*logScale n ℓ * E := by
    have hm := Info.mean_mono P (fun z hz =>
      mul_le_mul_of_nonneg_left (cost_energy β₀ (A z,B z) hx.le) (show 0 ≤ 4*logScale n ℓ by positivity))
    rw [show (fun z => 4*logScale n ℓ * (2*energy ℓ β₀ (A z,B z))) =
      (fun z => (8*logScale n ℓ)*energy ℓ β₀ (A z,B z)) by funext z; ring, Info.mean_mul P (8*logScale n ℓ)] at hm
    exact hm
  have hboundR : P.mean (fun z => 4*logScale n ℓ *
      (((terrible (B z,A z)).card : ℝ) + ratio n ℓ * (badLeft (B z,A z)).card)) ≤ 8*logScale n ℓ * E := by
    have hbnd (z : α) : ((terrible (B z,A z)).card : ℝ) + ratio n ℓ * (badLeft (B z,A z)).card ≤
        2*energy ℓ β₀ (A z,B z) := by
      have hh := cost_energy β₀ (B z,A z) hx.le
      rw [energy_swap ℓ β₀ (A z,B z)] at hh
      exact hh
    have hm := Info.mean_mono P (fun z hz =>
      mul_le_mul_of_nonneg_left (hbnd z) (show 0 ≤ 4*logScale n ℓ by positivity))
    rw [show (fun z => 4*logScale n ℓ * (2*energy ℓ β₀ (A z,B z))) =
      (fun z => (8*logScale n ℓ)*energy ℓ β₀ (A z,B z)) by funext z; ring, Info.mean_mul P (8*logScale n ℓ)] at hm
    exact hm
  have hswap : (P.map (fun z => (B z,A z))).entropy = (P.map (fun z => (A z,B z))).entropy := by
    apply Info.entropy_fibers
    intro a b
    simp [and_comm]
  change P.condEntropy A B ≤ P.mean (fun z => 4*logScale n ℓ *
    (((terrible (A z,B z)).card : ℝ) + ratio n ℓ * (badLeft (A z,B z)).card)) + n*ratio n ℓ at hcL
  change P.condEntropy B A ≤ P.mean (fun z => 4*logScale n ℓ *
    (((terrible (B z,A z)).card : ℝ) + ratio n ℓ * (badLeft (B z,A z)).card)) + n*ratio n ℓ at hcR
  have hI := Info.mutualInfo_process P X Y f g
  change mutualInfo P A B ≤ mutualInfo P X Y at hI
  have hE : β₀*n*ratio n ℓ ≤ E := by
    have hm := Info.mean_mono P (fun z hz => energy_floor β₀ hβ hβ1 hx.le (by linarith) (A z,B z))
    rw [Info.mean_const] at hm
    exact hm
  have hE0 : 0 ≤ E := le_trans (by positivity) hE
  have hnx : 2*(n : ℝ)*ratio n ℓ ≤ (2/β₀)*logScale n ℓ*E := by
    have heq : β₀*(2/β₀)=2 := by field_simp
    have hmul := mul_le_mul_of_nonneg_left hE (show 0 ≤ 2/β₀ by positivity)
    have hAE := mul_le_mul_of_nonneg_left hA1 (show 0 ≤ (2/β₀)*E by positivity)
    nlinarith
  unfold Law.condEntropy at hcL hcR
  rw [hswap] at hcR
  unfold mutualInfo at hI
  change (P.map (fun z => (A z,B z))).entropy ≤ mutualInfo P X Y + (16+2/β₀)*logScale n ℓ*E
  unfold mutualInfo
  nlinarith
end BirthdayEntropy.Soundness.Code
theorem solution {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    {n ℓ : ℕ} (P : Law α) (X : α → β) (Y : α → γ)
    (f : β → Finset (Signed n)) (g : γ → Finset (Signed n))
    (β₀ : ℝ) (hβ : 0 < β₀) (hβ1 : β₀ ≤ 1)
    (hx : 0 < ratio n ℓ) (hxhalf : ratio n ℓ ≤ 1/2)
    (hcross : ∀ z, 0 < P.mass z → CrossConsistent (f (X z),g (Y z))) :
    (P.map (fun z => (f (X z),g (Y z)))).entropy ≤ mutualInfo P X Y +
      (16+2/β₀)*logScale n ℓ * P.mean (fun z => energy ℓ β₀ (f (X z),g (Y z))) := by
  exact BirthdayEntropy.Soundness.Code.generic_flatten_entropy P X Y f g β₀ hβ hβ1 hx hxhalf hcross
