-- Prove2me | solution 1 for CubicSurface27.linesOf_finite_to_27
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-22T10:14:18.609999+00:00
-- url     : https://prove2.me/submissions/c27a152e-f115-4dfd-91f4-aa28d85a0b5a

import Mathlib
import Definitions.Def_cubic_surface_27_layer
import Theorems.Thm_CubicSurface27_exists_line
import Theorems.Thm_CubicSurface27_five_planes_through_line
import Theorems.Thm_CubicSurface27_residual_two_lines

/-! ## meets_exactly_one (from Sol_F27_meets_exactly_one) -/

open MvPolynomial

namespace F27MeetAux

open CubicSurface27

/-! ### Degree-3 monomials are products of three variables -/

lemma exists_single_add {n : ℕ} (m : Fin 4 →₀ ℕ) (hm : m.degree = n + 1) :
    ∃ i m', m = m' + Finsupp.single i 1 ∧ m'.degree = n := by
  have hne : m ≠ 0 := by
    rintro rfl; simp at hm
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
  have hle : Finsupp.single i 1 ≤ m := by
    rw [Finsupp.single_le_iff]; simp at hi; omega
  refine ⟨i, m - Finsupp.single i 1, (tsub_add_cancel_of_le hle).symm, ?_⟩
  have h := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
  rw [map_add, Finsupp.degree_single, hm] at h
  omega

lemma monomial_deg3 (m : Fin 4 →₀ ℕ) (hm : m.degree = 3) :
    ∃ a b c : Fin 4, monomial m (1 : ℂ) = X a * X b * X c := by
  obtain ⟨c, m1, rfl, h1⟩ := exists_single_add (n := 2) m hm
  obtain ⟨b, m2, rfl, h2⟩ := exists_single_add (n := 1) m1 h1
  obtain ⟨a, m3, rfl, h3⟩ := exists_single_add (n := 0) m2 h2
  rw [Finsupp.degree_eq_zero_iff] at h3
  subst h3
  refine ⟨a, b, c, ?_⟩
  simp [X, monomial_mul]

/-- Induction principle for homogeneous cubics. -/
lemma cubic_induction (P : MvPolynomial (Fin 4) ℂ → Prop)
    (h0 : P 0) (hadd : ∀ F G, P F → P G → P (F + G))
    (hsmul : ∀ (r : ℂ) F, P F → P (r • F))
    (hX : ∀ a b c : Fin 4, P (X a * X b * X c))
    (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) : P F := by
  rw [F.as_sum]
  refine Finset.sum_induction _ P hadd h0 ?_
  intro m hm
  have hdeg : m.degree = 3 := by
    have := hF (mem_support_iff.mp hm)
    rw [Finsupp.degree_eq_weight_one]
    exact this
  obtain ⟨a, b, c, habc⟩ := monomial_deg3 m hdeg
  have : monomial m (coeff m F) = coeff m F • monomial m (1 : ℂ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, habc]
  exact hsmul _ _ (hX a b c)

/-! ### First-order Taylor expansion of a cubic along a direction -/

lemma taylor3 (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (x w : Fin 4 → ℂ) :
    ∃ q : ℂ, ∀ t : ℂ, eval (x + t • w) F =
      eval x F + t * (∑ i, w i * eval x (pderiv i F)) + t ^ 2 * q + t ^ 3 * eval w F := by
  refine cubic_induction (fun F => ∃ q : ℂ, ∀ t : ℂ, eval (x + t • w) F =
      eval x F + t * (∑ i, w i * eval x (pderiv i F)) + t ^ 2 * q + t ^ 3 * eval w F)
    ?_ ?_ ?_ ?_ F hF
  · exact ⟨0, fun t => by simp⟩
  · rintro F G ⟨q1, h1⟩ ⟨q2, h2⟩
    refine ⟨q1 + q2, fun t => ?_⟩
    simp only [map_add, h1 t, h2 t, mul_add, Finset.sum_add_distrib]
    ring
  · rintro r F ⟨q, h⟩
    refine ⟨r * q, fun t => ?_⟩
    simp only [smul_eval, Derivation.map_smul, h t]
    have : ∑ i, w i * (r * eval x (pderiv i F)) = r * ∑ i, w i * eval x (pderiv i F) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [this]; ring
  · intro a b c
    refine ⟨x a * w b * w c + w a * x b * w c + w a * w b * x c, fun t => ?_⟩
    simp [Derivation.leibniz, pderiv_X, Pi.single_apply, mul_add, add_mul,
      Finset.sum_add_distrib, apply_ite (eval x), mul_ite, Finset.sum_ite_eq]
    ring

/-- The gradient of `F` at a point `x` of a line `W ⊆ V(F)` kills `W`. -/
lemma grad_tangent (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F)
    (W : Submodule ℂ (Fin 4 → ℂ)) (hW : W ∈ linesOf F) (x w : Fin 4 → ℂ)
    (hx : x ∈ W) (hw : w ∈ W) : ∑ i, w i * eval x (pderiv i F) = 0 := by
  obtain ⟨q, hq⟩ := taylor3 F hF x w
  have e1 := hq 1
  have e2 := hq (-1)
  rw [hW.2 _ (W.add_mem hx (W.smul_mem _ hw)), hW.2 x hx, hW.2 w hw] at e1 e2
  linear_combination (e2 - e1) / 2

/-! ### A 2-dimensional subspace inside a union of three 2-dimensional subspaces -/

lemma eq_of_le_union3 (M a b c : Submodule ℂ (Fin 4 → ℂ)) (hM : Module.finrank ℂ M = 2)
    (ha : Module.finrank ℂ a = 2) (hb : Module.finrank ℂ b = 2) (hc : Module.finrank ℂ c = 2)
    (h : ∀ x ∈ M, x ∈ a ∨ x ∈ b ∨ x ∈ c) : M = a ∨ M = b ∨ M = c := by
  let e := Module.finBasisOfFinrankEq ℂ M hM
  set u : Fin 4 → ℂ := ((e 0 : M) : Fin 4 → ℂ) with hu
  set v : Fin 4 → ℂ := ((e 1 : M) : Fin 4 → ℂ) with hv
  have huM : u ∈ M := (e 0).2
  have hvM : v ∈ M := (e 1).2
  have key : ∀ S : Submodule ℂ (Fin 4 → ℂ), Module.finrank ℂ S = 2 → u ∈ S → v ∈ S → M = S := by
    intro S hS huS hvS
    have hle : M ≤ S := by
      intro m hm
      have hsum := congrArg Subtype.val (e.sum_repr ⟨m, hm⟩)
      simp only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul] at hsum
      rw [← hsum]
      exact S.add_mem (S.smul_mem _ huS) (S.smul_mem _ hvS)
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hM, hS])
  let T : Fin 3 → Submodule ℂ (Fin 4 → ℂ) := ![a, b, c]
  have hT : ∀ t : ℂ, ∃ i : Fin 3, u + t • v ∈ T i := by
    intro t
    rcases h _ (M.add_mem huM (M.smul_mem t hvM)) with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  choose f hf using hT
  obtain ⟨s, t, hst, hfst⟩ := Finite.exists_ne_map_eq_of_infinite f
  have h1 := hf s
  have h2 := hf t
  rw [hfst] at h1
  set S := T (f t)
  have hvS : v ∈ S := by
    have hd : (s - t) • v ∈ S := by
      have := S.sub_mem h1 h2
      convert this using 1
      rw [sub_smul]; abel
    exact (S.smul_mem_iff (sub_ne_zero.mpr hst)).mp hd
  have huS : u ∈ S := by
    have := S.sub_mem h2 (S.smul_mem t hvS)
    simpa using this
  have hS2 : Module.finrank ℂ S = 2 := by
    show Module.finrank ℂ (T (f t)) = 2
    generalize f t = i
    fin_cases i <;> assumption
  have hMS := key S hS2 huS hvS
  show M = a ∨ M = b ∨ M = c
  generalize hi : f t = i at hMS
  simp only [S, hi] at hMS
  fin_cases i
  · exact Or.inl hMS
  · exact Or.inr (Or.inl hMS)
  · exact Or.inr (Or.inr hMS)

/-! ### The two halves of `meets_exactly_one` -/

lemma at_least_one (F : MvPolynomial (Fin 4) ℂ)
    (P : Submodule ℂ (Fin 4 → ℂ)) (hP : Module.finrank ℂ P = 3)
    (a b c : Submodule ℂ (Fin 4 → ℂ))
    (hPF : ∀ x ∈ P, eval x F = 0 → x ∈ a ∨ x ∈ b ∨ x ∈ c)
    (M : Submodule ℂ (Fin 4 → ℂ)) (hM : M ∈ linesOf F) :
    M ⊓ a ≠ ⊥ ∨ M ⊓ b ≠ ⊥ ∨ M ⊓ c ≠ ⊥ := by
  have hne : M ⊓ P ≠ ⊥ := by
    intro h
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq M P
    rw [h, finrank_bot, hM.1, hP] at h1
    have h2 := Submodule.finrank_le (M ⊔ P)
    rw [Module.finrank_fin_fun] at h2
    omega
  obtain ⟨x, ⟨hxM, hxP⟩, hx0⟩ := Submodule.ne_bot_iff _ |>.mp hne
  rcases hPF x hxP (hM.2 x hxM) with h | h | h
  · exact Or.inl ((Submodule.ne_bot_iff _).mpr ⟨x, ⟨hxM, h⟩, hx0⟩)
  · exact Or.inr (Or.inl ((Submodule.ne_bot_iff _).mpr ⟨x, ⟨hxM, h⟩, hx0⟩))
  · exact Or.inr (Or.inr ((Submodule.ne_bot_iff _).mpr ⟨x, ⟨hxM, h⟩, hx0⟩))

lemma not_both (F : MvPolynomial (Fin 4) ℂ)
    (hF : IsCubicForm F) (hsm : IsSmoothCubic F)
    (P : Submodule ℂ (Fin 4 → ℂ)) (hP : Module.finrank ℂ P = 3)
    (a b c : Submodule ℂ (Fin 4 → ℂ)) (ha : a ∈ linesOf F) (hb : b ∈ linesOf F)
    (hc : c ∈ linesOf F) (hab : a ≠ b)
    (haP : a ≤ P) (hbP : b ≤ P)
    (hPF : ∀ x ∈ P, eval x F = 0 → x ∈ a ∨ x ∈ b ∨ x ∈ c)
    (M : Submodule ℂ (Fin 4 → ℂ)) (hM : M ∈ linesOf F)
    (hMa : M ≠ a) (hMb : M ≠ b) (hMc : M ≠ c) :
    ¬ (M ⊓ a ≠ ⊥ ∧ M ⊓ b ≠ ⊥) := by
  rintro ⟨hxa, hyb⟩
  obtain ⟨x, ⟨hxM, hxa⟩, hx0⟩ := Submodule.ne_bot_iff _ |>.mp hxa
  obtain ⟨y, ⟨hyM, hyb⟩, hy0⟩ := Submodule.ne_bot_iff _ |>.mp hyb
  suffices hMP : M ≤ P by
    rcases eq_of_le_union3 M a b c hM.1 ha.1 hb.1 hc.1
      (fun z hz => hPF z (hMP hz) (hM.2 z hz)) with h | h | h
    · exact hMa h
    · exact hMb h
    · exact hMc h
  have hx1 : Module.finrank ℂ (ℂ ∙ x) = 1 := finrank_span_singleton hx0
  by_cases hy' : y ∈ ℂ ∙ x
  · -- `x` lies on `a`, `b` and `M`: use the tangent plane at `x`
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy'
    have hr : r ≠ 0 := by rintro rfl; simp at hy0
    have hxb : x ∈ b := (b.smul_mem_iff hr).mp hyb
    let g : (Fin 4 → ℂ) →ₗ[ℂ] ℂ := ∑ i, (eval x (pderiv i F)) • LinearMap.proj i
    have hg : ∀ w, g w = ∑ i, w i * eval x (pderiv i F) := by
      intro w; simp [g, mul_comm]
    have hker : ∀ W ∈ linesOf F, x ∈ W → W ≤ LinearMap.ker g := by
      intro W hW hxW w hw
      rw [LinearMap.mem_ker, hg]
      exact grad_tangent F hF W hW x w hxW hw
    have hktop : LinearMap.ker g ≠ ⊤ := by
      intro htop
      obtain ⟨i, hi⟩ := hsm x hx0 (hM.2 x hxM)
      have : Pi.single i 1 ∈ LinearMap.ker g := htop ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, hg] at this
      apply hi
      simpa [Pi.single_apply] using this
    have hk : Module.finrank ℂ (LinearMap.ker g) < 4 := by
      have := Submodule.finrank_lt hktop
      rwa [Module.finrank_fin_fun] at this
    have hlt : a < a ⊔ b := by
      refine lt_of_le_of_ne le_sup_left (fun h => hab ?_)
      exact (Submodule.eq_of_le_of_finrank_eq (h ▸ le_sup_right : b ≤ a)
        (by rw [ha.1, hb.1])).symm
    have h3 := Submodule.finrank_lt_finrank_of_lt hlt
    rw [ha.1] at h3
    have h4 := Submodule.finrank_mono (sup_le haP hbP)
    have hsupP : a ⊔ b = P := Submodule.eq_of_le_of_finrank_eq (sup_le haP hbP) (by omega)
    have hPk : P ≤ LinearMap.ker g := hsupP ▸ sup_le (hker a ha hxa) (hker b hb hxb)
    have h5 := Submodule.finrank_mono hPk
    have hPk' : P = LinearMap.ker g := Submodule.eq_of_le_of_finrank_eq hPk (by omega)
    exact hPk' ▸ hker M hM hxM
  · -- `x` and `y` span `M`, and both lie in `P`
    have hlt : ℂ ∙ x < (ℂ ∙ x) ⊔ (ℂ ∙ y) :=
      lt_of_le_of_ne le_sup_left (fun h => hy' (h ▸ Submodule.mem_sup_right
        (Submodule.mem_span_singleton_self y)))
    have h2 := Submodule.finrank_lt_finrank_of_lt hlt
    have hle : (ℂ ∙ x) ⊔ (ℂ ∙ y) ≤ M ⊓ P := by
      rw [sup_le_iff, Submodule.span_singleton_le_iff_mem, Submodule.span_singleton_le_iff_mem]
      exact ⟨⟨hxM, haP hxa⟩, ⟨hyM, hbP hyb⟩⟩
    have h3 := Submodule.finrank_mono hle
    have h5 := Submodule.finrank_mono (inf_le_left : M ⊓ P ≤ M)
    have h6 := hM.1
    have h4 : M ⊓ P = M := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
    exact inf_eq_left.mp h4

end F27MeetAux

open CubicSurface27 F27MeetAux in
theorem M27.meets_exactly_one (F : MvPolynomial (Fin 4) ℂ)
    (hF : IsCubicForm F) (hsm : IsSmoothCubic F)
    (P : Submodule ℂ (Fin 4 → ℂ)) (hP : Module.finrank ℂ P = 3)
    (a b c : Submodule ℂ (Fin 4 → ℂ)) (ha : a ∈ linesOf F) (hb : b ∈ linesOf F)
    (hc : c ∈ linesOf F) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haP : a ≤ P) (hbP : b ≤ P) (hcP : c ≤ P)
    (hPF : ∀ x ∈ P, MvPolynomial.eval x F = 0 → x ∈ a ∨ x ∈ b ∨ x ∈ c)
    (M : Submodule ℂ (Fin 4 → ℂ)) (hM : M ∈ linesOf F)
    (hMa : M ≠ a) (hMb : M ≠ b) (hMc : M ≠ c) :
    (M ⊓ a ≠ ⊥ ∨ M ⊓ b ≠ ⊥ ∨ M ⊓ c ≠ ⊥) ∧
      ¬ (M ⊓ a ≠ ⊥ ∧ M ⊓ b ≠ ⊥) ∧ ¬ (M ⊓ a ≠ ⊥ ∧ M ⊓ c ≠ ⊥) ∧
      ¬ (M ⊓ b ≠ ⊥ ∧ M ⊓ c ≠ ⊥) := by
  refine ⟨at_least_one F P hP a b c hPF M hM, ?_, ?_, ?_⟩
  · exact not_both F hF hsm P hP a b c ha hb hc hab haP hbP hPF M hM hMa hMb hMc
  · exact not_both F hF hsm P hP a c b ha hc hb hac haP hcP
      (fun x hx h => by rcases hPF x hx h with h | h | h <;> tauto) M hM hMa hMc hMb
  · exact not_both F hF hsm P hP b c a hb hc ha hbc hbP hcP
      (fun x hx h => by rcases hPF x hx h with h | h | h <;> tauto) M hM hMb hMc hMa

/-! ## meet_count_ten (from Sol_F27_meet_count_ten) -/

namespace F27TenAux

/-! ### A 2-dimensional subspace inside a union of three 2-dimensional subspaces -/

lemma eq_of_le_union3 (M a b c : Submodule ℂ (Fin 4 → ℂ)) (hM : Module.finrank ℂ M = 2)
    (ha : Module.finrank ℂ a = 2) (hb : Module.finrank ℂ b = 2) (hc : Module.finrank ℂ c = 2)
    (h : ∀ x ∈ M, x ∈ a ∨ x ∈ b ∨ x ∈ c) : M = a ∨ M = b ∨ M = c := by
  let e := Module.finBasisOfFinrankEq ℂ M hM
  set u : Fin 4 → ℂ := ((e 0 : M) : Fin 4 → ℂ) with hu
  set v : Fin 4 → ℂ := ((e 1 : M) : Fin 4 → ℂ) with hv
  have huM : u ∈ M := (e 0).2
  have hvM : v ∈ M := (e 1).2
  have key : ∀ S : Submodule ℂ (Fin 4 → ℂ), Module.finrank ℂ S = 2 → u ∈ S → v ∈ S → M = S := by
    intro S hS huS hvS
    have hle : M ≤ S := by
      intro m hm
      have hsum := congrArg Subtype.val (e.sum_repr ⟨m, hm⟩)
      simp only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul] at hsum
      rw [← hsum]
      exact S.add_mem (S.smul_mem _ huS) (S.smul_mem _ hvS)
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hM, hS])
  let T : Fin 3 → Submodule ℂ (Fin 4 → ℂ) := ![a, b, c]
  have hT : ∀ t : ℂ, ∃ i : Fin 3, u + t • v ∈ T i := by
    intro t
    rcases h _ (M.add_mem huM (M.smul_mem t hvM)) with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  choose f hf using hT
  obtain ⟨s, t, hst, hfst⟩ := Finite.exists_ne_map_eq_of_infinite f
  have h1 := hf s
  have h2 := hf t
  rw [hfst] at h1
  set S := T (f t)
  have hvS : v ∈ S := by
    have hd : (s - t) • v ∈ S := by
      have := S.sub_mem h1 h2
      convert this using 1
      rw [sub_smul]; abel
    exact (S.smul_mem_iff (sub_ne_zero.mpr hst)).mp hd
  have huS : u ∈ S := by
    have := S.sub_mem h2 (S.smul_mem t hvS)
    simpa using this
  have hS2 : Module.finrank ℂ S = 2 := by
    show Module.finrank ℂ (T (f t)) = 2
    generalize f t = i
    fin_cases i <;> assumption
  have hMS := key S hS2 huS hvS
  show M = a ∨ M = b ∨ M = c
  generalize hi : f t = i at hMS
  simp only [S, hi] at hMS
  fin_cases i
  · exact Or.inl hMS
  · exact Or.inr (Or.inl hMS)
  · exact Or.inr (Or.inr hMS)

open CubicSurface27

/-- The lines of `P` other than `L` are exactly `b` and `c`. -/
lemma piece_eq (F : MvPolynomial (Fin 4) ℂ) (L P b c : Submodule ℂ (Fin 4 → ℂ))
    (hL : L ∈ linesOf F) (hb : b ∈ linesOf F) (hc : c ∈ linesOf F)
    (hLb : L ≠ b) (hLc : L ≠ c) (hbP : b ≤ P) (hcP : c ≤ P)
    (hPF : ∀ x ∈ P, MvPolynomial.eval x F = 0 → x ∈ L ∨ x ∈ b ∨ x ∈ c)
    (M : Submodule ℂ (Fin 4 → ℂ)) :
    (M ∈ linesOf F ∧ M ≤ P ∧ M ≠ L) ↔ (M = b ∨ M = c) := by
  constructor
  · rintro ⟨hM, hMP, hML⟩
    rcases eq_of_le_union3 M L b c hM.1 hL.1 hb.1 hc.1
      (fun z hz => hPF z (hMP hz) (hM.2 z hz)) with h | h | h
    · exact absurd h hML
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · exact ⟨hb, hbP, Ne.symm hLb⟩
    · exact ⟨hc, hcP, Ne.symm hLc⟩

/-- A line `M ≠ L` meeting `L` spans a plane with it. -/
lemma finrank_sup_eq_three (L M : Submodule ℂ (Fin 4 → ℂ)) (hL : Module.finrank ℂ L = 2)
    (hM : Module.finrank ℂ M = 2) (hML : M ≠ L) (hmeet : M ⊓ L ≠ ⊥) :
    Module.finrank ℂ ↥(M ⊔ L) = 3 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq M L
  have h2 : Module.finrank ℂ ↥(M ⊓ L) ≠ 0 := fun h =>
    hmeet (Submodule.finrank_eq_zero.mp h)
  have hlt : L < M ⊔ L := by
    refine lt_of_le_of_ne le_sup_right (fun h => hML ?_)
    exact Submodule.eq_of_le_of_finrank_eq (h ▸ le_sup_left : M ≤ L) (by rw [hM, hL])
  have h3 := Submodule.finrank_lt_finrank_of_lt hlt
  omega

/-- Two distinct 2-dimensional subspaces of a 3-dimensional space meet nontrivially. -/
lemma inf_ne_bot_of_le_plane (P X Y : Submodule ℂ (Fin 4 → ℂ)) (hP : Module.finrank ℂ P = 3)
    (hX : Module.finrank ℂ X = 2) (hY : Module.finrank ℂ Y = 2) (hXP : X ≤ P) (hYP : Y ≤ P) :
    X ⊓ Y ≠ ⊥ := by
  intro h
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq X Y
  rw [h, finrank_bot] at h1
  have h2 : Module.finrank ℂ ↥(X ⊔ Y) ≤ Module.finrank ℂ P :=
    Submodule.finrank_mono (sup_le hXP hYP)
  omega

end F27TenAux

open CubicSurface27 F27TenAux in
theorem M27.meet_count_ten (F : MvPolynomial (Fin 4) ℂ)
    (hF : IsCubicForm F) (hsm : IsSmoothCubic F)
    (L : Submodule ℂ (Fin 4 → ℂ)) (hL : L ∈ linesOf F) :
    {M | M ∈ linesOf F ∧ M ≠ L ∧ M ⊓ L ≠ ⊥}.ncard = 10 := by
  classical
  set Pl := {P : Submodule ℂ (Fin 4 → ℂ) | Module.finrank ℂ P = 3 ∧ L ≤ P ∧
      ∃ M ∈ linesOf F, M ≤ P ∧ M ≠ L} with hPl
  set N := {M | M ∈ linesOf F ∧ M ≠ L ∧ M ⊓ L ≠ ⊥} with hN
  have h5 : Pl.ncard = 5 := five_planes_through_line F hF hsm L hL
  have hPlfin : Pl.Finite := Set.finite_of_ncard_ne_zero (by rw [h5]; norm_num)
  -- each plane of `Pl` carries exactly two lines other than `L`
  have hpiece : ∀ P ∈ Pl, ∃ b c : Submodule ℂ (Fin 4 → ℂ), b ≠ c ∧
      ∀ M, (M ∈ N ∧ M ⊔ L = P) ↔ (M = b ∨ M = c) := by
    rintro P ⟨hP, hLP, hExt⟩
    obtain ⟨b, hb, c, hc, hLb, hLc, hbc, hbP, hcP, hPF⟩ :=
      residual_two_lines F hF hsm L hL P hP hLP hExt
    refine ⟨b, c, hbc, fun M => ?_⟩
    rw [← piece_eq F L P b c hL hb hc hLb hLc hbP hcP hPF M]
    constructor
    · rintro ⟨⟨hM, hML, _⟩, rfl⟩
      exact ⟨hM, le_sup_left, hML⟩
    · rintro ⟨hM, hMP, hML⟩
      have hmeet := inf_ne_bot_of_le_plane P M L hP hM.1 hL.1 hMP hLP
      refine ⟨⟨hM, hML, hmeet⟩, ?_⟩
      exact Submodule.eq_of_le_of_finrank_eq (sup_le hMP hLP)
        (by rw [finrank_sup_eq_three L M hL.1 hM.1 hML hmeet, hP])
  have hmap : ∀ M ∈ N, M ⊔ L ∈ Pl := by
    rintro M ⟨hM, hML, hmeet⟩
    exact ⟨finrank_sup_eq_three L M hL.1 hM.1 hML hmeet, le_sup_right, M, hM, le_sup_left, hML⟩
  -- `N` is finite: it is covered by the finitely many two-element pieces
  have hNfin : N.Finite := by
    refine (hPlfin.biUnion (t := fun P => {M | M ∈ N ∧ M ⊔ L = P}) ?_).subset ?_
    · intro P hP
      obtain ⟨b, c, _, hbc⟩ := hpiece P hP
      refine (Set.toFinite ({b, c} : Set _)).subset ?_
      intro M hM
      rcases (hbc M).mp hM with rfl | rfl <;> simp
    · intro M hM
      exact Set.mem_biUnion (hmap M hM) ⟨hM, rfl⟩
  rw [Set.ncard_eq_toFinset_card N hNfin]
  rw [Set.ncard_eq_toFinset_card Pl hPlfin] at h5
  rw [Finset.card_eq_sum_card_fiberwise (f := fun M => M ⊔ L) (t := hPlfin.toFinset)
    (fun M hM => by simpa using hmap M (by simpa using hM))]
  rw [Finset.sum_const_nat (m := 2), h5]
  intro P hP
  obtain ⟨b, c, hbc, hiff⟩ := hpiece P (by simpa using hP)
  have : hNfin.toFinset.filter (fun M => M ⊔ L = P) = {b, c} := by
    ext M
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_insert,
      Finset.mem_singleton]
    exact hiff M
  rw [this, Finset.card_pair hbc]

/-! ## tritangent_through_line (from Sol_F27_tritangent_through_line) -/

open CubicSurface27 in
theorem M27.tritangent_through_line (F : MvPolynomial (Fin 4) ℂ)
    (hF : IsCubicForm F) (hsm : IsSmoothCubic F)
    (L : Submodule ℂ (Fin 4 → ℂ)) (hL : L ∈ linesOf F) :
    ∃ P : Submodule ℂ (Fin 4 → ℂ), Module.finrank ℂ P = 3 ∧ L ≤ P ∧
      ∃ b ∈ linesOf F, ∃ c ∈ linesOf F, L ≠ b ∧ L ≠ c ∧ b ≠ c ∧ b ≤ P ∧ c ≤ P ∧
        ∀ x ∈ P, MvPolynomial.eval x F = 0 → x ∈ L ∨ x ∈ b ∨ x ∈ c := by
  have h5 := five_planes_through_line F hF hsm L hL
  obtain ⟨P, hP, hLP, hM⟩ := Set.nonempty_of_ncard_ne_zero (by rw [h5]; norm_num)
  exact ⟨P, hP, hLP, residual_two_lines F hF hsm L hL P hP hLP hM⟩

/-! ## Top-level count -/

open MvPolynomial

namespace F27Glue

/-- Purely combinatorial count: a triangle `a, b, c` such that every other element is
`R`-related to exactly one of its vertices, and each vertex has exactly 10 neighbours,
forces `3 + 3 · 8 = 27` elements. -/
lemma count27 {α : Type*} (S : Set α) (hS : S.Finite) (R : α → α → Prop)
    (a b c : α) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Rba : R b a) (Rca : R c a) (Rab : R a b) (Rcb : R c b) (Rac : R a c) (Rbc : R b c)
    (hone : ∀ M ∈ S, M ≠ a → M ≠ b → M ≠ c →
      (R M a ∨ R M b ∨ R M c) ∧ ¬ (R M a ∧ R M b) ∧ ¬ (R M a ∧ R M c) ∧ ¬ (R M b ∧ R M c))
    (hNa : {M | M ∈ S ∧ M ≠ a ∧ R M a}.ncard = 10)
    (hNb : {M | M ∈ S ∧ M ≠ b ∧ R M b}.ncard = 10)
    (hNc : {M | M ∈ S ∧ M ≠ c ∧ R M c}.ncard = 10) :
    S.ncard = 27 := by
  classical
  set A := {M | M ∈ S ∧ M ≠ a ∧ R M a} \ {b, c} with hA
  set B := {M | M ∈ S ∧ M ≠ b ∧ R M b} \ {a, c} with hB
  set C := {M | M ∈ S ∧ M ≠ c ∧ R M c} \ {a, b} with hC
  have hfin : ∀ T : Set α, T ⊆ S → T.Finite := fun T hT => hS.subset hT
  have cA : A.ncard = 8 := by
    rw [hA, Set.ncard_sdiff (by
      intro x hx; rcases hx with rfl | rfl
      · exact ⟨hb, hab.symm, Rba⟩
      · exact ⟨hc, hac.symm, Rca⟩), hNa, Set.ncard_pair hbc]
  have cB : B.ncard = 8 := by
    rw [hB, Set.ncard_sdiff (by
      intro x hx; rcases hx with rfl | rfl
      · exact ⟨ha, hab, Rab⟩
      · exact ⟨hc, hbc.symm, Rcb⟩), hNb, Set.ncard_pair hac]
  have cC : C.ncard = 8 := by
    rw [hC, Set.ncard_sdiff (by
      intro x hx; rcases hx with rfl | rfl
      · exact ⟨ha, hac, Rac⟩
      · exact ⟨hb, hbc, Rbc⟩), hNc, Set.ncard_pair hab]
  have hAS : A ⊆ S := fun x hx => hx.1.1
  have hBS : B ⊆ S := fun x hx => hx.1.1
  have hCS : C ⊆ S := fun x hx => hx.1.1
  have dAB : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro M ⟨⟨hMS, hMa, hRa⟩, hM1⟩ ⟨⟨_, hMb, hRb⟩, hM2⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hM1 hM2
    exact (hone M hMS hMa hMb hM1.2).2.1 ⟨hRa, hRb⟩
  have dABC : Disjoint (A ∪ B) C := by
    rw [Set.disjoint_left]
    rintro M hM ⟨⟨hMS, hMc, hRc⟩, hM3⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hM3
    rcases hM with ⟨⟨_, _, hRa⟩, _⟩ | ⟨⟨_, _, hRb⟩, _⟩
    · exact (hone M hMS hM3.1 hM3.2 hMc).2.2.1 ⟨hRa, hRc⟩
    · exact (hone M hMS hM3.1 hM3.2 hMc).2.2.2 ⟨hRb, hRc⟩
  have hsplit : S \ {a, b, c} = A ∪ B ∪ C := by
    ext M
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
      Set.mem_union, hA, hB, hC, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hMS, hMa, hMb, hMc⟩
      rcases (hone M hMS hMa hMb hMc).1 with h | h | h
      · exact Or.inl (Or.inl ⟨⟨hMS, hMa, h⟩, hMb, hMc⟩)
      · exact Or.inl (Or.inr ⟨⟨hMS, hMb, h⟩, hMa, hMc⟩)
      · exact Or.inr ⟨⟨hMS, hMc, h⟩, hMa, hMb⟩
    · rintro ((⟨⟨hMS, hMa, _⟩, hMb, hMc⟩ | ⟨⟨hMS, hMb, _⟩, hMa, hMc⟩) | ⟨⟨hMS, hMc, _⟩, hMa, hMb⟩)
      <;> exact ⟨hMS, hMa, hMb, hMc⟩
  have h3 : ({a, b, c} : Set α).ncard = 3 := Set.ncard_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hsub : ({a, b, c} : Set α) ⊆ S := by
    intro x hx; rcases hx with rfl | rfl | rfl <;> assumption
  have key := Set.ncard_sdiff_add_ncard_of_subset hsub hS
  rw [hsplit, Set.ncard_union_eq dABC ((hfin _ hAS).union (hfin _ hBS)) (hfin _ hCS),
    Set.ncard_union_eq dAB (hfin _ hAS) (hfin _ hBS), cA, cB, cC, h3] at key
  omega

/-- Two distinct 2-dimensional subspaces of a 3-dimensional space meet nontrivially. -/
lemma inf_ne_bot_of_le_plane (P X Y : Submodule ℂ (Fin 4 → ℂ)) (hP : Module.finrank ℂ P = 3)
    (hX : Module.finrank ℂ X = 2) (hY : Module.finrank ℂ Y = 2) (hXP : X ≤ P) (hYP : Y ≤ P) :
    X ⊓ Y ≠ ⊥ := by
  intro h
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq X Y
  rw [h, finrank_bot] at h1
  have h2 : Module.finrank ℂ ↥(X ⊔ Y) ≤ Module.finrank ℂ P :=
    Submodule.finrank_mono (sup_le hXP hYP)
  omega

end F27Glue

open CubicSurface27 F27Glue M27 in
theorem solution (F : MvPolynomial (Fin 4) ℂ)
    (hF : IsCubicForm F) (hsm : IsSmoothCubic F) (hfin : (linesOf F).Finite) :
    (linesOf F).ncard = 27 := by
  obtain ⟨a, ha⟩ := exists_line F hF
  obtain ⟨P, hP, haP, b, hb, c, hc, hab, hac, hbc, hbP, hcP, hPF⟩ :=
    tritangent_through_line F hF hsm a ha
  have meet : ∀ X Y, X ∈ linesOf F → Y ∈ linesOf F → X ≤ P → Y ≤ P → X ⊓ Y ≠ ⊥ :=
    fun X Y hX hY hXP hYP => inf_ne_bot_of_le_plane P X Y hP hX.1 hY.1 hXP hYP
  exact count27 (linesOf F) hfin (fun M X => M ⊓ X ≠ ⊥) a b c ha hb hc hab hac hbc
    (meet b a hb ha hbP haP) (meet c a hc ha hcP haP) (meet a b ha hb haP hbP)
    (meet c b hc hb hcP hbP) (meet a c ha hc haP hcP) (meet b c hb hc hbP hcP)
    (fun M hM hMa hMb hMc =>
      meets_exactly_one F hF hsm P hP a b c ha hb hc hab hac hbc haP hbP hcP hPF M hM hMa hMb hMc)
    (meet_count_ten F hF hsm a ha) (meet_count_ten F hF hsm b hb) (meet_count_ten F hF hsm c hc)
