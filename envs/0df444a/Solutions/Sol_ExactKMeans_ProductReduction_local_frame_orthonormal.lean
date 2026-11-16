-- Prove2me | solution 1 for ExactKMeans.ProductReduction.local_frame_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-15T18:49:00.722335+00:00
-- url     : https://prove2.me/submissions/f6b5df74-7a83-4ce4-8976-52f271b9f4da

import Definitions.Def_ExactKMeans_ProductReduction_Placement

open scoped BigOperators Classical
open Finset
open ExactKMeans.ProductReduction

namespace KMeansFrame

lemma inner_unit (d j k : ℕ) (hj : j < d) (_hk : k < d) :
    inner ℝ (unit d j) (unit d k) = if j = k then 1 else 0 := by
  unfold unit
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct]
  have hj' : ∀ x : Fin d, ((x : ℕ) = j) ↔ x = ⟨j, hj⟩ := fun x => by simp [Fin.ext_iff]
  simp [hj', Finset.sum_ite_eq']


section generic
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {b : ℕ}

/-- Orthonormality of an indexed family, Kronecker form. -/
abbrev ON (f : Fin b → V) : Prop := ∀ j k, inner ℝ (f j) (f k) = if j = k then (1 : ℝ) else 0
/-- `x` is orthogonal to every member of `f`. -/
abbrev Perp (f : Fin b → V) (x : V) : Prop := ∀ j, inner ℝ (f j) x = 0

noncomputable def bar (f : Fin b → V) : V := (1 / Real.sqrt b) • ∑ j, f j

lemma inner_bar_left (f : Fin b → V) (x : V) :
    inner ℝ (bar f) x = (1 / Real.sqrt b) * ∑ j, inner ℝ (f j) x := by
  simp [bar, inner_smul_left, sum_inner]

lemma inner_bar_right (f : Fin b → V) (x : V) :
    inner ℝ x (bar f) = (1 / Real.sqrt b) * ∑ j, inner ℝ (f j) x := by
  rw [real_inner_comm]; exact inner_bar_left f x

lemma bar_perp {f : Fin b → V} {x : V} (h : Perp f x) : inner ℝ (bar f) x = 0 := by
  simp [inner_bar_left, h _]

lemma inner_mem_bar {f : Fin b → V} (hf : ON f) (k : Fin b) :
    inner ℝ (f k) (bar f) = 1 / Real.sqrt b := by
  rw [inner_bar_right]
  simp [real_inner_comm (f k), hf]

lemma inner_bar_bar {f : Fin b → V} (hf : ON f) (hb : 0 < b) :
    inner ℝ (bar f) (bar f) = 1 := by
  rw [inner_bar_left]
  simp only [inner_mem_bar hf, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr (by exact_mod_cast hb)
  have h2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt (by positivity)
  field_simp
  linarith

noncomputable def dev (f : Fin b → V) (j : Fin b) : V := f j - (1 / Real.sqrt b) • bar f

lemma sqrt_facts (hb : 0 < b) : 0 < Real.sqrt b ∧ Real.sqrt b ^ 2 = b :=
  ⟨Real.sqrt_pos.mpr (by exact_mod_cast hb), Real.sq_sqrt (by positivity)⟩

lemma dev_perp {f : Fin b → V} {x : V} (h : Perp f x) (j : Fin b) :
    inner ℝ (dev f j) x = 0 := by
  simp [dev, inner_sub_left, inner_smul_left, bar_perp h, h j]

lemma dev_bar {f : Fin b → V} (hf : ON f) (hb : 0 < b) (j : Fin b) :
    inner ℝ (dev f j) (bar f) = 0 := by
  simp only [dev, inner_sub_left, inner_smul_left, inner_mem_bar hf, inner_bar_bar hf hb]
  simp

lemma inner_bar_mem {f : Fin b → V} (hf : ON f) (k : Fin b) :
    inner ℝ (bar f) (f k) = 1 / Real.sqrt b := by
  rw [real_inner_comm]; exact inner_mem_bar hf k

lemma dev_dev {f : Fin b → V} (hf : ON f) (hb : 0 < b) (j k : Fin b) :
    inner ℝ (dev f j) (dev f k) = (if j = k then (1 : ℝ) else 0) - 1 / b := by
  obtain ⟨hs, h2⟩ := sqrt_facts (b := b) hb
  simp only [dev, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    inner_mem_bar hf, inner_bar_mem hf, inner_bar_bar hf hb, RCLike.conj_to_real]
  rw [hf]
  have : (1 / Real.sqrt b) * (1 / Real.sqrt b) = 1 / b := by field_simp; rw [h2]
  split_ifs <;> linear_combination (-1 : ℝ) * this

lemma perp_of_cross {f g : Fin b → V} (h : ∀ j k, inner ℝ (f j) (g k) = 0) :
    (∀ k, Perp f (g k)) ∧ Perp f (bar g) ∧ (∀ j, Perp g (f j)) ∧ Perp g (bar f) := by
  refine ⟨fun k j => h j k, fun j => ?_, fun j k => by rw [real_inner_comm]; exact h j k, fun k => ?_⟩
  · rw [inner_bar_right]; simp [real_inner_comm, h]
  · rw [inner_bar_right]; simp [h]

lemma dev_dev_cross {f g : Fin b → V}
    (h : ∀ j k, inner ℝ (f j) (g k) = 0) (j k : Fin b) :
    inner ℝ (dev f j) (dev g k) = 0 := by
  obtain ⟨h1, h2, _, _⟩ := perp_of_cross h
  show inner ℝ (dev f j) (g k - (1 / Real.sqrt b) • bar g) = 0
  rw [inner_sub_right, inner_smul_right, dev_perp (h1 k), dev_perp h2]; simp

/-- The local frame: Gram computation from the Gram data of its ingredients. -/
lemma frame_gram (U W : Fin b → V) (L LP : V) (c s : ℝ) (hcs : s ^ 2 + c ^ 2 = 1) (hb : 0 < b)
    (hUU : ∀ j k, inner ℝ (U j) (U k) = (if j = k then (1 : ℝ) else 0) - 1 / b)
    (hWW : ∀ j k, inner ℝ (W j) (W k) = (if j = k then (1 : ℝ) else 0) - 1 / b)
    (hUW : ∀ j k, inner ℝ (U j) (W k) = 0)
    (hUL : ∀ j, inner ℝ (U j) L = 0) (hULP : ∀ j, inner ℝ (U j) LP = 0)
    (hWL : ∀ j, inner ℝ (W j) L = 0) (hWLP : ∀ j, inner ℝ (W j) LP = 0)
    (hLL : inner ℝ L L = 1) (hPP : inner ℝ LP LP = 1) (hLP : inner ℝ L LP = 0) :
    let E := fun j => c • U j + s • W j + (1 / Real.sqrt b) • L
    let P := fun j => (-s) • U j + c • W j + (1 / Real.sqrt b) • LP
    ON E ∧ ON P ∧ ∀ j k, inner ℝ (E j) (P k) = 0 := by
  obtain ⟨hs, h2⟩ := sqrt_facts (b := b) hb
  have hWU : ∀ j k, inner ℝ (W j) (U k) = 0 := fun j k => by rw [real_inner_comm, hUW]
  have hLU : ∀ j, inner ℝ L (U j) = 0 := fun j => by rw [real_inner_comm, hUL]
  have hLW : ∀ j, inner ℝ L (W j) = 0 := fun j => by rw [real_inner_comm, hWL]
  have hPU : ∀ j, inner ℝ LP (U j) = 0 := fun j => by rw [real_inner_comm, hULP]
  have hPW : ∀ j, inner ℝ LP (W j) = 0 := fun j => by rw [real_inner_comm, hWLP]
  have hPL : inner ℝ LP L = 0 := by rw [real_inner_comm, hLP]
  have key : (1 / Real.sqrt b) * (1 / Real.sqrt b) = 1 / b := by
    field_simp; rw [h2]
  refine ⟨fun j k => ?_, fun j k => ?_, fun j k => ?_⟩ <;>
  · simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      hUU, hWW, hUW, hWU, hUL, hULP, hWL, hWLP, hLU, hLW, hPU, hPW, hLL, hPP, hLP,
      RCLike.conj_to_real]
    split_ifs <;> nlinarith [key]

end generic

section concrete
variable (p : Parameters)

lemma d_eq : p.d = 2 * p.b + 1 := rfl

lemma e_on : ON (e p) := fun j k => by
  have hj := j.isLt; have hk := k.isLt
  show inner ℝ (unit p.d (2 * j.val)) (unit p.d (2 * k.val)) = _
  rw [inner_unit _ _ _ (by rw [d_eq]; omega) (by rw [d_eq]; omega)]
  have : (2 * j.val = 2 * k.val) ↔ j = k := by rw [Fin.ext_iff]; omega
  simp only [this]

lemma ep_on : ON (ep p) := fun j k => by
  have hj := j.isLt; have hk := k.isLt
  show inner ℝ (unit p.d (2 * j.val + 1)) (unit p.d (2 * k.val + 1)) = _
  rw [inner_unit _ _ _ (by rw [d_eq]; omega) (by rw [d_eq]; omega)]
  have : (2 * j.val + 1 = 2 * k.val + 1) ↔ j = k := by rw [Fin.ext_iff]; omega
  simp only [this]

lemma e_ep (j k : Fin p.b) : inner ℝ (e p j) (ep p k) = 0 := by
  have hj := j.isLt; have hk := k.isLt
  show inner ℝ (unit p.d (2 * j.val)) (unit p.d (2 * k.val + 1)) = _
  rw [inner_unit _ _ _ (by rw [d_eq]; omega) (by rw [d_eq]; omega)]
  rw [if_neg (by omega)]

lemma e_axis : Perp (e p) (axis p) := fun j => by
  have hj := j.isLt
  show inner ℝ (unit p.d (2 * j.val)) (unit p.d (2 * p.b)) = _
  rw [inner_unit _ _ _ (by rw [d_eq]; omega) (by rw [d_eq]; omega)]
  rw [if_neg (by omega)]

lemma ep_axis : Perp (ep p) (axis p) := fun j => by
  have hj := j.isLt
  show inner ℝ (unit p.d (2 * j.val + 1)) (unit p.d (2 * p.b)) = _
  rw [inner_unit _ _ _ (by rw [d_eq]; omega) (by rw [d_eq]; omega)]
  rw [if_neg (by omega)]

lemma axis_axis : inner ℝ (axis p) (axis p) = 1 := by
  show inner ℝ (unit p.d (2 * p.b)) (unit p.d (2 * p.b)) = _
  rw [inner_unit _ _ _ (by rw [d_eq]; omega) (by rw [d_eq]; omega)]
  simp

lemma ebar_eq : ebar p = bar (e p) := rfl
lemma epbar_eq : epbar p = bar (ep p) := rfl

lemma localE_eq (i : Fin p.a) (j : Fin p.b) : localE p i j =
    Real.cos (p.theta i) • dev (e p) j + Real.sin (p.theta i) • dev (ep p) j +
      (1 / Real.sqrt p.b) • localBar p i := rfl

lemma localEP_eq (i : Fin p.a) (j : Fin p.b) : localEP p i j =
    (-Real.sin (p.theta i)) • dev (e p) j + Real.cos (p.theta i) • dev (ep p) j +
      (1 / Real.sqrt p.b) • localBarP p i := rfl

/-- All Gram data of the selector ingredients. -/
lemma gram_data (i : Fin p.a) :
    (∀ j, inner ℝ (dev (e p) j) (localBar p i) = 0) ∧
    (∀ j, inner ℝ (dev (e p) j) (localBarP p i) = 0) ∧
    (∀ j, inner ℝ (dev (ep p) j) (localBar p i) = 0) ∧
    (∀ j, inner ℝ (dev (ep p) j) (localBarP p i) = 0) ∧
    inner ℝ (localBar p i) (localBar p i) = 1 ∧
    inner ℝ (localBarP p i) (localBarP p i) = 1 ∧
    inner ℝ (localBar p i) (localBarP p i) = 0 ∧
    (∀ j, inner ℝ (dev (e p) j) (axis p) = 0) ∧
    (∀ j, inner ℝ (dev (ep p) j) (axis p) = 0) ∧
    inner ℝ (localBar p i) (axis p) = 0 := by
  have hb := p.b_pos
  obtain ⟨-, hEbarP, -, hPbarE⟩ := perp_of_cross (e_ep p)
  have hEE := inner_bar_bar (e_on p) hb
  have hPP := inner_bar_bar (ep_on p) hb
  have hEP : inner ℝ (bar (e p)) (bar (ep p)) = 0 := bar_perp hEbarP
  have hPE : inner ℝ (bar (ep p)) (bar (e p)) = 0 := bar_perp hPbarE
  have hEa : inner ℝ (bar (e p)) (axis p) = 0 := bar_perp (e_axis p)
  have hPa : inner ℝ (bar (ep p)) (axis p) = 0 := bar_perp (ep_axis p)
  have haE : inner ℝ (axis p) (bar (e p)) = 0 := by rw [real_inner_comm, hEa]
  have haP : inner ℝ (axis p) (bar (ep p)) = 0 := by rw [real_inner_comm, hPa]
  have h1 := dev_bar (e_on p) hb
  have h2 := dev_perp hEbarP
  have h3 := dev_bar (ep_on p) hb
  have h4 := dev_perp hPbarE
  have h5 := dev_perp (e_axis p)
  have h6 := dev_perp (ep_axis p)
  have hax := axis_axis p
  have hθ := Real.sin_sq_add_cos_sq (p.theta i)
  have hβ := Real.sin_sq_add_cos_sq p.beta
  simp only [localBar, localBarP, ebar_eq, epbar_eq, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
    h1, h2, h3, h4, h5, h6, hEE, hPP, hEP, hPE, hEa, hPa, haE, haP, hax]
  refine ⟨fun _ => by ring, fun _ => by ring, fun _ => by ring, fun _ => by ring, ?_, ?_, ?_,
    fun _ => trivial, fun _ => trivial, by ring⟩
  · linear_combination hθ
  · linear_combination (Real.sin p.beta ^ 2) * hθ + hβ
  · ring

lemma frame (i : Fin p.a) :
    ON (localE p i) ∧ ON (localEP p i) ∧ ∀ j k, inner ℝ (localE p i j) (localEP p i k) = 0 := by
  have hb := p.b_pos
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, -, -, -⟩ := gram_data p i
  have := frame_gram (dev (e p)) (dev (ep p)) (localBar p i) (localBarP p i)
    (Real.cos (p.theta i)) (Real.sin (p.theta i)) (Real.sin_sq_add_cos_sq _) hb
    (dev_dev (e_on p) hb) (dev_dev (ep_on p) hb) (dev_dev_cross (e_ep p)) g1 g2 g3 g4 g5 g6 g7
  exact this

lemma localE_axis (i : Fin p.a) (j : Fin p.b) : inner ℝ (localE p i j) (axis p) = 0 := by
  obtain ⟨-, -, -, -, -, -, -, g8, g9, g10⟩ := gram_data p i
  rw [localE_eq]
  simp only [inner_add_left, inner_smul_left, g8, g9, g10, RCLike.conj_to_real]; ring

end concrete

end KMeansFrame

open KMeansFrame in
theorem solution (p : Parameters) (i : Fin p.a) :
    (∀ j k : Fin p.b, inner ℝ (localE p i j) (localE p i k) = if j = k then (1 : ℝ) else 0) ∧
    (∀ j k : Fin p.b, inner ℝ (localEP p i j) (localEP p i k) = if j = k then (1 : ℝ) else 0) ∧
    (∀ j k : Fin p.b, inner ℝ (localE p i j) (localEP p i k) = 0) ∧
    (∀ j : Fin p.b, inner ℝ (localE p i j) (axis p) = 0) ∧
    inner ℝ (axis p) (axis p) = 1 := by
  obtain ⟨hE, hP, hEP⟩ := frame p i
  exact ⟨hE, hP, hEP, localE_axis p i, axis_axis p⟩
