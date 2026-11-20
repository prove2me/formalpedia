-- Prove2me | solution 1 for BinarySketchTruncation.Opposite.Supplement.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:16:05.503184+00:00
-- url     : https://prove2.me/submissions/f131a69c-11db-49bb-9f0e-047ca161c3f7

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_Supplement_UnateEvaluation
import Theorems.Thm_BinarySketchTruncation_Opposite_Supplement_proposition_3

section
namespace BinarySketchTruncation.Dev.Thm2
open BinarySketchTruncation.Opposite BinarySketchTruncation.Opposite.Supplement
open Matrix

lemma bit2 (a s : Bit) : a + s + s = a := by revert a s; decide
lemma bit4 (x d a : Bit) : x + d + (a + x) = a + d := by revert x d a; decide

lemma vec_add_cancel {m : ℕ} (x a : Vec m) : x + a + a = x := by
  funext i; exact bit2 _ _

lemma map_toReal {S T : Type} [Fintype S] [Fintype T] [DecidableEq T]
    (μ : PMF S) (f : S → T) (t : T) :
    ((μ.map f) t).toReal = ∑ s, (μ s).toReal * (if f s = t then 1 else 0) := by
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : f s = t
    · simp [h]
    · simp [h, Ne.symm h]
  · intro s _
    split_ifs
    · exact PMF.apply_ne_top _ _
    · simp

section part1
variable {n k : ℕ}

noncomputable def Bm (A : Matrix (Fin k) (Fin n) Bit) (e : Fin k ↪ Fin n) :
    Matrix (Fin k) (Fin k) Bit := fun i j => A i (e j)

noncomputable def Vf (A : Matrix (Fin k) (Fin n) Bit) (e : Fin k ↪ Fin n) (z : Vec n) : Vec k :=
  (Bm A e)⁻¹ *ᵥ (A *ᵥ z) + fun i => z (e i)

def Uf (e : Fin k ↪ Fin n) (d : Vec n) (z : Vec n) : Vec k := fun i => z (e i) + d (e i)

noncomputable def Psi (A : Matrix (Fin k) (Fin n) Bit) (e : Fin k ↪ Fin n) (d : Vec n)
    (z : Vec n) : Vec k × Vec k := (Uf e d z, Vf A e z)

lemma sum_Psi (A : Matrix (Fin k) (Fin n) Bit) (e : Fin k ↪ Fin n) (d z : Vec n) :
    (Psi A e d z).1 + (Psi A e d z).2 = (Bm A e)⁻¹ *ᵥ (A *ᵥ z) + fun i => d (e i) := by
  funext i
  simp only [Psi, Uf, Vf, Pi.add_apply]
  exact bit4 _ _ _

lemma A_single (A : Matrix (Fin k) (Fin n) Bit) (e : Fin k ↪ Fin n) (i : Fin k) :
    A *ᵥ Pi.single (e i) 1 = Bm A e *ᵥ Pi.single i 1 := by
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  rfl

lemma single_comp (e : Fin k ↪ Fin n) (i : Fin k) :
    (fun j => (Pi.single (e i) (1 : Bit) : Vec n) (e j)) = Pi.single i 1 := by
  funext j
  simp only [Pi.single_apply, e.injective.eq_iff]

lemma Vf_flip (A : Matrix (Fin k) (Fin n) Bit) (e : Fin k ↪ Fin n)
    (hB : IsUnit (Bm A e).det) (z : Vec n) (i : Fin k) :
    Vf A e (z + Pi.single (e i) 1) = Vf A e z := by
  have hinv : (Bm A e)⁻¹ *ᵥ (Bm A e *ᵥ (Pi.single i 1 : Vec k)) = Pi.single i 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB, Matrix.one_mulVec]
  unfold Vf
  rw [Matrix.mulVec_add, A_single, Matrix.mulVec_add, hinv]
  have : (fun j => (z + (Pi.single (e i) (1 : Bit) : Vec n)) (e j)) =
      (fun j => z (e j)) + Pi.single i 1 := by
    funext j
    simp only [Pi.add_apply]
    rw [← single_comp e i]
  rw [this]
  funext j
  simp only [Pi.add_apply]
  generalize ((Bm A e)⁻¹ *ᵥ (A *ᵥ z)) j = a
  generalize z (e j) = b
  generalize (Pi.single i 1 : Vec k) j = s
  revert a b s; decide

lemma Uf_flip (e : Fin k ↪ Fin n) (d z : Vec n) (i : Fin k) :
    Uf e d (z + Pi.single (e i) 1) = Uf e d z + Pi.single i 1 := by
  funext j
  simp only [Uf, Pi.add_apply, Pi.single_apply, e.injective.eq_iff]
  ring

lemma upd_flip1 (u : Vec k) (i : Fin k) :
    Function.update u i 1 + Pi.single i 1 = Function.update u i 0 := by
  funext j
  by_cases hj : j = i
  · subst hj; simp; decide
  · simp [Function.update_of_ne hj, Pi.single_eq_of_ne hj]

lemma upd_flip0 (u : Vec k) (i : Fin k) :
    Function.update u i 0 + Pi.single i 1 = Function.update u i 1 := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj, Pi.single_eq_of_ne hj]

lemma fz1 (z d : Vec n) (j : Fin n) (h : z j + d j = 1) :
    Function.update (z + d) j 0 + d = z + Pi.single j 1 ∧
      Function.update (z + d) j 1 + d = z := by
  constructor <;> funext m <;> by_cases hm : m = j
  · subst hm
    simp only [Pi.add_apply, Function.update_self, Pi.single_eq_same]
    revert h; generalize z m = a; generalize d m = b; revert a b; decide
  · simp only [Pi.add_apply, Function.update_of_ne hm, Pi.single_eq_of_ne hm, add_zero]
    exact bit2 _ _
  · subst hm
    simp only [Pi.add_apply, Function.update_self]
    revert h; generalize z m = a; generalize d m = b; revert a b; decide
  · simp only [Pi.add_apply, Function.update_of_ne hm]
    exact bit2 _ _

lemma fz0 (z d : Vec n) (j : Fin n) (h : z j + d j = 0) :
    Function.update (z + d) j 1 + d = z + Pi.single j 1 ∧
      Function.update (z + d) j 0 + d = z := by
  constructor <;> funext m <;> by_cases hm : m = j
  · subst hm
    simp only [Pi.add_apply, Function.update_self, Pi.single_eq_same]
    revert h; generalize z m = a; generalize d m = b; revert a b; decide
  · simp only [Pi.add_apply, Function.update_of_ne hm, Pi.single_eq_of_ne hm, add_zero]
    exact bit2 _ _
  · subst hm
    simp only [Pi.add_apply, Function.update_self]
    revert h; generalize z m = a; generalize d m = b; revert a b; decide
  · simp only [Pi.add_apply, Function.update_of_ne hm]
    exact bit2 _ _

lemma bool_le_false {a b : Bool} (h : a ≤ b) (hb : b = false) : a = false := by
  revert a b; decide

lemma bool_le_true {a b : Bool} (h : a ≤ b) (ha : a = true) : b = true := by
  revert a b; decide

noncomputable def cnt (f : Vec n → Bool) (A : Matrix (Fin k) (Fin n) Bit) (e : Fin k ↪ Fin n)
    (d : Vec n) (h : Bool) (q : Vec k × Vec k) : ℝ :=
  ∑ z, if f z = h ∧ Psi A e d z = q then 1 else 0

lemma cnt_mono_aux (f : Vec n → Bool) (A : Matrix (Fin k) (Fin n) Bit) (e : Fin k ↪ Fin n)
    (d : Vec n) (h h' : Bool) (q q' : Vec k × Vec k) (i : Fin k)
    (H : ∀ z, f z = h ∧ Psi A e d z = q → f (z + Pi.single (e i) 1) = h' ∧
      Psi A e d (z + Pi.single (e i) 1) = q') :
    cnt f A e d h q ≤ cnt f A e d h' q' := by
  unfold cnt
  calc (∑ z, if f z = h ∧ Psi A e d z = q then (1 : ℝ) else 0)
      ≤ ∑ z, if f (z + Pi.single (e i) 1) = h' ∧ Psi A e d (z + Pi.single (e i) 1) = q'
          then (1 : ℝ) else 0 := by
        refine Finset.sum_le_sum fun z _ => ?_
        by_cases hz : f z = h ∧ Psi A e d z = q
        · split_ifs with h1 <;> first | exact absurd (H z hz) h1 | norm_num
        · split_ifs <;> norm_num
    _ = ∑ z, if f z = h' ∧ Psi A e d z = q' then (1 : ℝ) else 0 := by
        have := Equiv.sum_comp (Equiv.addRight (Pi.single (e i) (1 : Bit) : Vec n))
          (fun z => if f z = h' ∧ Psi A e d z = q' then (1 : ℝ) else 0)
        simp only [Equiv.coe_addRight] at this
        convert this
        congr

lemma cnt_mono_false (f : Vec n → Bool) (d : Vec n)
    (hd : ∀ (z : Vec n) (i : Fin n), f (Function.update z i 0 + d) ≤ f (Function.update z i 1 + d))
    (A : Matrix (Fin k) (Fin n) Bit) (e : Fin k ↪ Fin n) (hB : IsUnit (Bm A e).det)
    (v u : Vec k) (i : Fin k) :
    cnt f A e d false (Function.update u i 1, v) ≤ cnt f A e d false (Function.update u i 0, v) := by
  refine cnt_mono_aux f A e d false false _ _ i ?_
  rintro z ⟨hf, hP⟩
  have hU : Uf e d z = Function.update u i 1 := congrArg Prod.fst hP
  have hV : Vf A e z = v := congrArg Prod.snd hP
  have h1 : z (e i) + d (e i) = 1 := by
    have := congrFun hU i
    simpa [Uf] using this
  obtain ⟨a1, a2⟩ := fz1 z d (e i) h1
  have hh := hd (z + d) (e i)
  rw [a1, a2] at hh
  refine ⟨bool_le_false hh hf, ?_⟩
  simp only [Psi]
  rw [Uf_flip, Vf_flip A e hB, hU, hV, upd_flip1]

lemma cnt_mono_true (f : Vec n → Bool) (d : Vec n)
    (hd : ∀ (z : Vec n) (i : Fin n), f (Function.update z i 0 + d) ≤ f (Function.update z i 1 + d))
    (A : Matrix (Fin k) (Fin n) Bit) (e : Fin k ↪ Fin n) (hB : IsUnit (Bm A e).det)
    (v u : Vec k) (i : Fin k) :
    cnt f A e d true (Function.update u i 0, v) ≤ cnt f A e d true (Function.update u i 1, v) := by
  refine cnt_mono_aux f A e d true true _ _ i ?_
  rintro z ⟨hf, hP⟩
  have hU : Uf e d z = Function.update u i 0 := congrArg Prod.fst hP
  have hV : Vf A e z = v := congrArg Prod.snd hP
  have h1 : z (e i) + d (e i) = 0 := by
    have := congrFun hU i
    simpa [Uf] using this
  obtain ⟨a1, a2⟩ := fz0 z d (e i) h1
  have hh := hd (z + d) (e i)
  rw [a1, a2] at hh
  refine ⟨bool_le_true hh hf, ?_⟩
  simp only [Psi]
  rw [Uf_flip, Vf_flip A e hB, hU, hV, upd_flip0]

open Classical in
noncomputable def Pexp (f : Vec n → Bool) (A : Matrix (Fin k) (Fin n) Bit) (e : Fin k ↪ Fin n)
    (d : Vec n) (h : Bool) : PMF (Vec k × Vec k) :=
  if hne : (Finset.univ.filter (fun z : Vec n => f z = h)).Nonempty then
    (PMF.uniformOfFinset _ hne).map (Psi A e d)
  else PMF.uniformOfFintype (Vec k × Vec k)

noncomputable def Nn (f : Vec n → Bool) (h : Bool) : ℝ := ∑ z, if f z = h then (1 : ℝ) else 0

lemma Pexp_key (f : Vec n → Bool) (A : Matrix (Fin k) (Fin n) Bit) (e : Fin k ↪ Fin n)
    (d : Vec n) (h : Bool) {T : Type} [Fintype T] [DecidableEq T] (G : Vec k × Vec k → T) (t : T) :
    Nn f h * (((Pexp f A e d h).map G) t).toReal =
      ∑ z, if f z = h ∧ G (Psi A e d z) = t then (1 : ℝ) else 0 := by
  classical
  by_cases hne : (Finset.univ.filter (fun z : Vec n => f z = h)).Nonempty
  · unfold Pexp
    rw [dif_pos hne, PMF.map_comp, map_toReal, Finset.mul_sum]
    have hN : Nn f h = ((Finset.univ.filter (fun z : Vec n => f z = h)).card : ℝ) := by
      unfold Nn; rw [Finset.sum_boole]
    have hpos : (0 : ℝ) < ((Finset.univ.filter (fun z : Vec n => f z = h)).card : ℝ) := by
      exact_mod_cast hne.card_pos
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [PMF.uniformOfFinset_apply, hN]
    by_cases hz : f z = h
    · have : z ∈ Finset.univ.filter (fun z : Vec n => f z = h) := by simp [hz]
      by_cases hg : G (Psi A e d z) = t
      · simp [this, hz, hg, hpos.ne']
      · simp [this, hz, hg]
    · have : z ∉ Finset.univ.filter (fun z : Vec n => f z = h) := by simp [hz]
      simp [this, hz]
  · have h0 : ∀ z, f z ≠ h := by
      intro z hz
      exact hne ⟨z, by simp [hz]⟩
    have hN : Nn f h = 0 := Finset.sum_eq_zero fun z _ => by simp [h0 z]
    rw [hN, zero_mul]
    exact (Finset.sum_eq_zero fun z _ => by simp [h0 z]).symm

lemma Nn_pos (f : Vec n → Bool) (h : Bool)
    (hne : (Finset.univ.filter (fun z : Vec n => f z = h)).Nonempty) : 0 < Nn f h := by
  classical
  have hN : Nn f h = ((Finset.univ.filter (fun z : Vec n => f z = h)).card : ℝ) := by
    unfold Nn; rw [Finset.sum_boole]
  rw [hN]
  exact_mod_cast hne.card_pos

lemma Pexp_mono (f : Vec n → Bool) (A : Matrix (Fin k) (Fin n) Bit) (e : Fin k ↪ Fin n)
    (d : Vec n) (h : Bool) (q q' : Vec k × Vec k) (hc : cnt f A e d h q ≤ cnt f A e d h q') :
    (Pexp f A e d h q).toReal ≤ (Pexp f A e d h q').toReal := by
  classical
  by_cases hne : (Finset.univ.filter (fun z : Vec n => f z = h)).Nonempty
  · have hp := Nn_pos f h hne
    have k1 := Pexp_key f A e d h (id : Vec k × Vec k → Vec k × Vec k) q
    have k2 := Pexp_key f A e d h (id : Vec k × Vec k → Vec k × Vec k) q'
    rw [PMF.map_id] at k1 k2
    have e1 : cnt f A e d h q = ∑ z, if f z = h ∧ Psi A e d z = q then (1 : ℝ) else 0 := rfl
    have e2 : cnt f A e d h q' = ∑ z, if f z = h ∧ Psi A e d z = q' then (1 : ℝ) else 0 := rfl
    simp only [id] at k1 k2
    rw [← e1] at k1
    rw [← e2] at k2
    rw [← k1, ← k2] at hc
    exact le_of_mul_le_mul_left hc hp
  · unfold Pexp
    rw [dif_neg hne]
    simp

lemma fjm_gen {n : ℕ} (f : Vec n → Bool) : ∀ {T : Type} [DecidableEq T] (s : Vec n → T) (h : Bool) (t : T),
      functionJointMass f s h t = (∑ z, if f z = h ∧ s z = t then (1 : ℝ) else 0) /
        Fintype.card (Vec n) := by
  classical
  intro T _ s h t
  unfold functionJointMass uniformProbability uniformMean
  congr
  funext x
  by_cases c : f x = h ∧ s x = t <;> simp [c]

theorem part1 (f : Vec n → Bool) (d : Vec n)
    (hd : ∀ (z : Vec n) (i : Fin n), f (Function.update z i 0 + d) ≤ f (Function.update z i 1 + d))
    (A : Matrix (Fin k) (Fin n) Bit) (e : Fin k ↪ Fin n) (hB : IsUnit (Bm A e).det) :
    FunctionDominates f (fun z => z ∘ e) (fun z => A.mulVec z) := by
  classical
  set P := Pexp f A e d with hP
  have h₀ : ∀ (v u : Vec k) (i : Fin k),
      (P false (Function.update u i 1, v)).toReal ≤
        (P false (Function.update u i 0, v)).toReal := fun v u i =>
    Pexp_mono f A e d false _ _ (cnt_mono_false f d hd A e hB v u i)
  have h₁ : ∀ (v u : Vec k) (i : Fin k),
      (P true (Function.update u i 0, v)).toReal ≤
        (P true (Function.update u i 1, v)).toReal := fun v u i =>
    Pexp_mono f A e d true _ _ (cnt_mono_true f d hd A e hB v u i)
  obtain ⟨K', ⟨hK1, hK2⟩, hK3⟩ := proposition_3 P h₀ h₁
  set B := Bm A e with hBdef
  set dE : Vec k := fun i => d (e i) with hdE
  have hBinv : ∀ w : Vec k, B *ᵥ (B⁻¹ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]
  have hBinv' : ∀ w : Vec k, B⁻¹ *ᵥ (B *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB, Matrix.one_mulVec]
  let eqv : Vec k ≃ Vec k :=
    { toFun := fun y => B⁻¹ *ᵥ y + dE
      invFun := fun t => B *ᵥ (t + dE)
      left_inv := fun y => by
        simp only [vec_add_cancel, hBinv]
      right_inv := fun t => by
        simp only [hBinv', vec_add_cancel] }
  have hCpos : (0 : ℝ) < Fintype.card (Vec n) := by exact_mod_cast Fintype.card_pos
  have fjm := @fjm_gen n f
  refine ⟨fun x y => K' (x + dE) (eqv y), ⟨fun x y => hK1 _ _, fun x => ?_⟩, ?_⟩
  · have := Equiv.sum_comp eqv (fun t => K' (x + dE) t)
    rw [this]
    exact hK2 _
  · intro h y
    -- left side
    have L : functionJointMass f (fun z => A.mulVec z) h y =
        Nn f h / Fintype.card (Vec n) *
          (((P h).map (fun uv => uv.1 + uv.2)) (eqv y)).toReal := by
      rw [fjm, div_mul_eq_mul_div, hP, Pexp_key]
      congr 1
      refine Finset.sum_congr rfl fun z _ => ?_
      have : (A *ᵥ z = y) ↔ ((Psi A e d z).1 + (Psi A e d z).2 = eqv y) := by
        rw [sum_Psi]
        show _ ↔ B⁻¹ *ᵥ (A *ᵥ z) + dE = B⁻¹ *ᵥ y + dE
        rw [add_left_inj]
        constructor
        · intro h'; rw [h']
        · intro h'
          have := congrArg (fun w => B *ᵥ w) h'
          simpa only [hBinv] using this
      simp only [this]
    have R : ∀ x : Vec k, functionJointMass f (fun z => z ∘ e) h x =
        Nn f h / Fintype.card (Vec n) * (((P h).map Prod.fst) (x + dE)).toReal := by
      intro x
      rw [fjm, div_mul_eq_mul_div, hP, Pexp_key]
      congr 1
      refine Finset.sum_congr rfl fun z _ => ?_
      have : (z ∘ e = x) ↔ ((Psi A e d z).1 = x + dE) := by
        show _ ↔ ((fun i => z (e i)) + dE = x + dE)
        rw [add_left_inj]
        rfl
      simp only [this]
    rw [L]
    have hK3' := hK3 h (eqv y)
    simp only at hK3'
    rw [hK3', Finset.mul_sum]
    simp_rw [R, mul_assoc]
    exact (Equiv.sum_comp (Equiv.addRight dE) (fun i => Nn f h / Fintype.card (Vec n) *
      (((PMF.map Prod.fst (P h)) i).toReal * K' i (eqv y)))).symm

end part1

section part2

noncomputable def err {n : ℕ} {T : Type} (f : Vec n → Bool) (s : Vec n → T) (g : T → Bool) : ℝ :=
  uniformProbability (fun z => g (s z) ≠ f z)

lemma err_eq {n : ℕ} {T : Type} [Fintype T] [DecidableEq T] (f : Vec n → Bool) (s : Vec n → T)
    (g : T → Bool) :
    err f s g = ∑ x, ∑ h, (if g x ≠ h then (1 : ℝ) else 0) * functionJointMass f s h x := by
  classical
  have hz : ∀ z, ∑ x, ∑ h, (if g x ≠ h then (1 : ℝ) else 0) *
      (if f z = h ∧ s z = x then (1 : ℝ) else 0) = if g (s z) ≠ f z then 1 else 0 := by
    intro z
    rw [Finset.sum_eq_single (s z)]
    · rw [Finset.sum_eq_single (f z)]
      · simp
      · intro h _ hne; simp [Ne.symm hne]
      · simp
    · intro x _ hx
      apply Finset.sum_eq_zero
      intro h _
      simp [Ne.symm hx]
    · simp
  have hnum : (∑ z, if g (s z) ≠ f z then (1 : ℝ) else 0) =
      ∑ x, ∑ h, (if g x ≠ h then (1 : ℝ) else 0) *
        (∑ z, if f z = h ∧ s z = x then (1 : ℝ) else 0) := by
    simp_rw [Finset.mul_sum]
    calc (∑ z, if g (s z) ≠ f z then (1 : ℝ) else 0)
        = ∑ z, ∑ x, ∑ h, (if g x ≠ h then (1 : ℝ) else 0) *
            (if f z = h ∧ s z = x then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl fun z _ => (hz z).symm
      _ = ∑ x, ∑ z, ∑ h, (if g x ≠ h then (1 : ℝ) else 0) *
            (if f z = h ∧ s z = x then (1 : ℝ) else 0) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun x _ => by
          rw [Finset.sum_comm]
  unfold err uniformProbability uniformMean
  refine (?_ : _ = (∑ z, if g (s z) ≠ f z then (1 : ℝ) else 0) /
      Fintype.card (Vec n)).trans ?_
  · congr 1
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases c : g (s z) ≠ f z <;> simp [c]
  rw [hnum, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [fjm_gen, mul_div_assoc]

lemma minErr_le {n : ℕ} {T : Type} [Fintype T] (f : Vec n → Bool) (s : Vec n → T) (g : T → Bool) :
    minimumError f s ≤ err f s g := by
  classical
  unfold minimumError
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ g))

lemma minErr_attained {n : ℕ} {T : Type} [Fintype T] (f : Vec n → Bool) (s : Vec n → T) :
    ∃ g : T → Bool, minimumError f s = err f s g := by
  classical
  obtain ⟨g, -, hg⟩ := Finset.exists_min_image Finset.univ (fun g : T → Bool => err f s g)
    Finset.univ_nonempty
  refine ⟨g, le_antisymm (minErr_le f s g) ?_⟩
  unfold minimumError
  apply Finset.le_min'
  intro y hy
  obtain ⟨g', -, rfl⟩ := Finset.mem_image.1 hy
  exact hg g' (Finset.mem_univ _)

lemma dpi {n : ℕ} {S T : Type} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (f : Vec n → Bool) (s : Vec n → S) (t : Vec n → T) (hd : FunctionDominates f s t) :
    minimumError f s ≤ minimumError f t := by
  classical
  obtain ⟨K, ⟨hK0, hK1⟩, hKJ⟩ := hd
  obtain ⟨g, hg⟩ := minErr_attained f t
  set w : S → Bool → ℝ := fun x b =>
    ∑ h, (if b ≠ h then (1 : ℝ) else 0) * functionJointMass f s h x with hw
  have step1 : err f t g = ∑ x, ∑ y, K x y * w x (g y) := by
    rw [err_eq]
    simp_rw [hKJ]
    simp only [hw, Finset.mul_sum]
    refine (Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun h _ => ?_
    ring
  let g' : S → Bool := fun x => if w x true ≤ w x false then true else false
  have hmin : ∀ x b, w x (g' x) ≤ w x b := by
    intro x b
    simp only [g']
    split_ifs with hc
    · cases b
      · exact hc
      · exact le_rfl
    · cases b
      · exact le_rfl
      · exact (not_le.1 hc).le
  have step2 : err f s g' = ∑ x, w x (g' x) := err_eq f s g'
  have step3 : ∑ x, w x (g' x) ≤ ∑ x, ∑ y, K x y * w x (g y) := by
    refine Finset.sum_le_sum fun x _ => ?_
    calc w x (g' x) = ∑ y, K x y * w x (g' x) := by rw [← Finset.sum_mul, hK1 x, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hmin x _) (hK0 x y)
  calc minimumError f s ≤ err f s g' := minErr_le f s g'
    _ ≤ err f t g := by rw [step2, step1]; exact step3
    _ = minimumError f t := hg.symm

end part2

section part3
variable {n k : ℕ}

noncomputable def Sel (e : Fin k ↪ Fin n) : Matrix (Fin k) (Fin n) Bit :=
  fun i j => if j = e i then 1 else 0

lemma Sel_mulVec (e : Fin k ↪ Fin n) (z : Vec n) : Sel e *ᵥ z = z ∘ e := by
  funext i
  simp [Matrix.mulVec, dotProduct, Sel]

lemma Bm_Sel (e : Fin k ↪ Fin n) : Bm (Sel e) e = 1 := by
  funext i j
  simp only [Bm, Sel, e.injective.eq_iff, Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

lemma unit_Sel (e : Fin k ↪ Fin n) : IsUnit (Bm (Sel e) e).det := by
  rw [Bm_Sel]; simp

lemma fullRank_of_info (A : Matrix (Fin k) (Fin n) Bit) (e : Fin k ↪ Fin n)
    (hB : IsUnit (Bm A e).det) : FullRowRank A := by
  unfold FullRowRank
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h1 : c ᵥ* Bm A e = 0 := by
    funext j
    have := congrFun hc (e j)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    simpa [Matrix.vecMul, dotProduct, Bm] using this
  have h2 : c = 0 := by
    have := congrArg (fun w => w ᵥ* (Bm A e)⁻¹) h1
    simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hB] using this
  rw [h2]; rfl

lemma exists_info (A : Matrix (Fin k) (Fin n) Bit) (hA : FullRowRank A) :
    ∃ e : Fin k ↪ Fin n, IsUnit (Bm A e).det := by
  classical
  have hrank : A.rank = k := by
    rw [Matrix.rank_eq_finrank_span_row]
    have := finrank_span_eq_card hA
    simp only [Fintype.card_fin] at this
    exact this
  obtain ⟨κ, f, hf, hspan, hli⟩ := exists_linearIndependent' Bit A.col
  have : Fintype κ := Fintype.ofInjective f hf
  have hcard : Fintype.card κ = k := by
    rw [← hrank, Matrix.rank_eq_finrank_span_cols, ← hspan, finrank_span_eq_card hli]
  let σ : Fin k ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let e : Fin k ↪ Fin n := ⟨fun i => f (σ i), fun x y hxy => σ.injective (hf hxy)⟩
  refine ⟨e, ?_⟩
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]
  exact hli.comp σ σ.injective

end part3

section part4
variable {n : ℕ}

theorem part2 (f : Vec n → Bool) (hf : IsUnate f) (k : ℕ) (hkn : k ≤ n) :
    optimalLinearError f k = optimalProjectionError f k ∧
      (∃ A : Matrix (Fin k) (Fin n) Bit, FullRowRank A ∧
        minimumError f (fun z => A.mulVec z) = optimalLinearError f k) ∧
      (∃ e : Fin k ↪ Fin n,
        minimumError f (fun z => z ∘ e) = optimalProjectionError f k) := by
  classical
  obtain ⟨d, hd⟩ := hf
  obtain ⟨e₁⟩ : Nonempty (Fin k ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hkn)
  have : Nonempty (Fin k ↪ Fin n) := ⟨e₁⟩
  have : Nonempty {A : Matrix (Fin k) (Fin n) Bit // FullRowRank A} :=
    ⟨⟨Sel e₁, fullRank_of_info _ e₁ (unit_Sel e₁)⟩⟩
  obtain ⟨A0, hA0⟩ := exists_eq_ciInf_of_finite
    (f := fun A : {A : Matrix (Fin k) (Fin n) Bit // FullRowRank A} =>
      minimumError f (fun z => A.val.mulVec z))
  obtain ⟨e0, he0⟩ := exists_eq_ciInf_of_finite
    (f := fun e : Fin k ↪ Fin n => minimumError f (fun z => z ∘ e))
  have c1 : optimalLinearError f k ≤ minimumError f (fun z => z ∘ e0) := by
    have hle := ciInf_le (Set.finite_range
      (fun A : {A : Matrix (Fin k) (Fin n) Bit // FullRowRank A} =>
        minimumError f (fun z => A.val.mulVec z))).bddBelow
      ⟨Sel e0, fullRank_of_info _ e0 (unit_Sel e0)⟩
    have : (fun z : Vec n => (Sel e0) *ᵥ z) = fun z => z ∘ e0 := funext (Sel_mulVec e0)
    simp only [this] at hle
    exact hle
  obtain ⟨eA, heA⟩ := exists_info A0.val A0.property
  have c2 : optimalProjectionError f k ≤ minimumError f (fun z => A0.val.mulVec z) := by
    have hle := ciInf_le (Set.finite_range
      (fun e : Fin k ↪ Fin n => minimumError f (fun z => z ∘ e))).bddBelow eA
    exact hle.trans (dpi f _ _ (part1 f d hd A0.val eA heA))
  have hlin : optimalLinearError f k = minimumError f (fun z => A0.val.mulVec z) := by
    unfold optimalLinearError; exact hA0.symm ▸ rfl
  have hproj : optimalProjectionError f k = minimumError f (fun z => z ∘ e0) := by
    unfold optimalProjectionError; exact he0.symm ▸ rfl
  have heq : optimalLinearError f k = optimalProjectionError f k :=
    le_antisymm (hproj ▸ c1) (hlin ▸ c2)
  exact ⟨heq, ⟨A0.val, A0.property, hlin.symm⟩, ⟨e0, hproj.symm⟩⟩

end part4
end BinarySketchTruncation.Dev.Thm2

namespace BinarySketchTruncation.Opposite.Supplement
open BinarySketchTruncation.Dev.Thm2

theorem chk_theorem_2 {n : ℕ} (f : Vec n → Bool) (hf : IsUnate f) :
    (∀ (k : ℕ) (A : Matrix (Fin k) (Fin n) Bit) (e : Fin k ↪ Fin n),
      IsInformationSet A e →
        FunctionDominates f (fun z => z ∘ e) (fun z => A.mulVec z)) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ n →
      optimalLinearError f k = optimalProjectionError f k ∧
      (∃ A : Matrix (Fin k) (Fin n) Bit, FullRowRank A ∧
        minimumError f (fun z => A.mulVec z) = optimalLinearError f k) ∧
      (∃ e : Fin k ↪ Fin n,
        minimumError f (fun z => z ∘ e) = optimalProjectionError f k)) := by
  refine ⟨fun k A e hI => ?_, fun k _ hkn => part2 f hf k hkn⟩
  obtain ⟨d, hd⟩ := hf
  exact part1 f d hd A e hI

end BinarySketchTruncation.Opposite.Supplement
end

theorem solution : type_of% @BinarySketchTruncation.Opposite.Supplement.chk_theorem_2 := @BinarySketchTruncation.Opposite.Supplement.chk_theorem_2
