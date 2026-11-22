-- Prove2me | solution 1 for CubicSurface27.exists_line
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-22T10:10:33.223546+00:00
-- url     : https://prove2.me/submissions/39892e10-7014-4cc8-aec3-0be5f64a99b0

import Definitions.Def_cubic_surface_27_layer

/-!
Every cubic surface contains a line (`CubicSurface27.exists_line`), no smoothness needed.

Route: the pencil `F_t = (1-t) G + t F` with `G = x₂x₀² + x₃x₁²`.  In the chart
`u₀ = e₀ + a e₂ + b e₃`, `u₁ = e₁ + c e₂ + d e₃`, the lines of `F_t` are the common zeros of
four polynomials `f_k ∈ ℂ[t,a,b,c,d]`, and `(f_k) + (t) = (t,a,b,c,d)`.  Krull's height
theorem gives a minimal prime `P ⊇ (f_k)` inside the origin ideal with `t ∉ P`; then
`ℂ[t] → ℂ[t,a,b,c,d]/P` is flat of finite presentation, hence an open map on spectra, so
`F_c` has a line for all but finitely many `c`.  The set of `c` for which `F_c` has a line is
closed (finitely many normalised charts with coordinates in a compact polydisc), hence all
of `ℂ`; take `c = 1`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open MvPolynomial

namespace ELAux

open CubicSurface27

/-- Symmetric trilinear polarization (normalized so that `polar3 F x x x = F x` for cubics). -/
noncomputable def polar3 (F : MvPolynomial (Fin 4) ℂ) (x y z : Fin 4 → ℂ) : ℂ :=
  (6 : ℂ)⁻¹ * (eval (x + y + z) F - eval (x + y) F - eval (y + z) F - eval (z + x) F
    + eval x F + eval y F + eval z F)

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

/-! ### Polarization identities -/

lemma polar3_zero (x y z : Fin 4 → ℂ) : polar3 0 x y z = 0 := by
  simp [polar3]

lemma polar3_add (F G : MvPolynomial (Fin 4) ℂ) (x y z : Fin 4 → ℂ) :
    polar3 (F + G) x y z = polar3 F x y z + polar3 G x y z := by
  simp only [polar3, map_add]; ring

lemma polar3_smul (r : ℂ) (F : MvPolynomial (Fin 4) ℂ) (x y z : Fin 4 → ℂ) :
    polar3 (r • F) x y z = r * polar3 F x y z := by
  simp only [polar3, smul_eval]; ring

lemma polar3_comm12 (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (x y z : Fin 4 → ℂ) :
    polar3 F x y z = polar3 F y x z := by
  refine cubic_induction (fun F => polar3 F x y z = polar3 F y x z) ?_ ?_ ?_ ?_ F hF
  · simp [polar3_zero]
  · intro F G hF hG; simp only [polar3_add, hF, hG]
  · intro r F hF; simp only [polar3_smul, hF]
  · intro a b c; simp [polar3]; ring

lemma polar3_comm13 (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (x y z : Fin 4 → ℂ) :
    polar3 F x y z = polar3 F z y x := by
  refine cubic_induction (fun F => polar3 F x y z = polar3 F z y x) ?_ ?_ ?_ ?_ F hF
  · simp [polar3_zero]
  · intro F G hF hG; simp only [polar3_add, hF, hG]
  · intro r F hF; simp only [polar3_smul, hF]
  · intro a b c; simp [polar3]; ring

/-- `F(u + ε d)` as a cubic in `ε`. -/
lemma expF (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (u d : Fin 4 → ℂ) (ε : ℂ) :
    eval (u + ε • d) F = eval u F + ε * (3 * polar3 F d u u) + ε ^ 2 * (3 * polar3 F d d u)
      + ε ^ 3 * eval d F := by
  refine cubic_induction (fun F => eval (u + ε • d) F = eval u F + ε * (3 * polar3 F d u u)
      + ε ^ 2 * (3 * polar3 F d d u) + ε ^ 3 * eval d F) ?_ ?_ ?_ ?_ F hF
  · simp [polar3_zero]
  · intro F G hF hG; simp only [polar3_add, map_add, hF, hG]; ring
  · intro r F hF; simp only [polar3_smul, smul_eval, hF]; ring
  · intro a b c; simp [polar3]; ring

/-- `B(u+εd, u+εd, w+εe)` as a cubic in `ε`. -/
lemma expB (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (u d w e : Fin 4 → ℂ) (ε : ℂ) :
    polar3 F (u + ε • d) (u + ε • d) (w + ε • e) = polar3 F u u w
      + ε * (2 * polar3 F d u w + polar3 F u u e)
      + ε ^ 2 * (polar3 F d d w + 2 * polar3 F d u e) + ε ^ 3 * polar3 F d d e := by
  refine cubic_induction (fun F => polar3 F (u + ε • d) (u + ε • d) (w + ε • e) = polar3 F u u w
      + ε * (2 * polar3 F d u w + polar3 F u u e)
      + ε ^ 2 * (polar3 F d d w + 2 * polar3 F d u e) + ε ^ 3 * polar3 F d d e)
    ?_ ?_ ?_ ?_ F hF
  · simp [polar3_zero]
  · intro F G hF hG; simp only [polar3_add, hF, hG]; ring
  · intro r F hF; simp only [polar3_smul, hF]; ring
  · intro a b c; simp [polar3]; ring

/-- `F(s u + t w)` as a binary cubic. -/
lemma expST (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (u w : Fin 4 → ℂ) (s t : ℂ) :
    eval (s • u + t • w) F = s ^ 3 * eval u F + 3 * s ^ 2 * t * polar3 F u u w
      + 3 * s * t ^ 2 * polar3 F w w u + t ^ 3 * eval w F := by
  refine cubic_induction (fun F => eval (s • u + t • w) F = s ^ 3 * eval u F
      + 3 * s ^ 2 * t * polar3 F u u w + 3 * s * t ^ 2 * polar3 F w w u + t ^ 3 * eval w F)
    ?_ ?_ ?_ ?_ F hF
  · simp [polar3_zero]
  · intro F G hF hG; simp only [polar3_add, map_add, hF, hG]; ring
  · intro r F hF; simp only [polar3_smul, smul_eval, hF]; ring
  · intro a b c; simp [polar3]; ring

/-! ### Differentiability of polynomial evaluation -/

@[fun_prop]
lemma differentiable_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → Fin 4 → ℂ) (hg : Differentiable ℂ g) (P : MvPolynomial (Fin 4) ℂ) :
    Differentiable ℂ (fun a => eval (g a) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p n hp =>
    simp only [eval_mul, eval_X]
    exact hp.mul (differentiable_pi.mp hg n)
/-! ### The chart map -/

/-- Chart coordinates `a ∈ ℂ⁴` give the line spanned by `chu0 a` and `chu1 a`. -/
def chu0 (v0 p q a : Fin 4 → ℂ) : Fin 4 → ℂ := v0 + a 0 • p + a 1 • q
def chu1 (v1 p q a : Fin 4 → ℂ) : Fin 4 → ℂ := v1 + a 2 • p + a 3 • q

/-- The four coefficients of the binary cubic `F(s u₀ + t u₁)` (up to the factors 3). -/
noncomputable def Φ (F : MvPolynomial (Fin 4) ℂ) (v0 v1 p q : Fin 4 → ℂ) (a : Fin 4 → ℂ) :
    Fin 4 → ℂ :=
  ![eval (chu0 v0 p q a) F,
    polar3 F (chu0 v0 p q a) (chu0 v0 p q a) (chu1 v1 p q a),
    polar3 F (chu1 v1 p q a) (chu1 v1 p q a) (chu0 v0 p q a),
    eval (chu1 v1 p q a) F]

lemma differentiable_Φ (F : MvPolynomial (Fin 4) ℂ) (v0 v1 p q : Fin 4 → ℂ) :
    Differentiable ℂ (Φ F v0 v1 p q) := by
  have h0 : Differentiable ℂ (chu0 v0 p q) := by unfold chu0; fun_prop
  have h1 : Differentiable ℂ (chu1 v1 p q) := by unfold chu1; fun_prop
  rw [differentiable_pi]
  intro i
  fin_cases i <;> simp [Φ, polar3] <;> fun_prop

/-! ### Every plane is in a normalised chart -/

/-- Standard basis vector. -/
noncomputable abbrev e (i : Fin 4) : Fin 4 → ℂ := Pi.single i 1

lemma exists_compl (i j : Fin 4) (hij : i ≠ j) :
    ∃ k l : Fin 4, i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l := by
  revert i j; decide

lemma fin4_cases (i j k l n : Fin 4) (h1 : i ≠ j) (h2 : i ≠ k) (h3 : i ≠ l) (h4 : j ≠ k)
    (h5 : j ≠ l) (h6 : k ≠ l) : n = i ∨ n = j ∨ n = k ∨ n = l := by
  revert i j k l n; decide

lemma cover (W : Submodule ℂ (Fin 4 → ℂ)) (hW : Module.finrank ℂ W = 2) :
    ∃ i j k l : Fin 4, (i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l) ∧
      ∃ a : Fin 4 → ℂ, ‖a‖ ≤ 1 ∧ chu0 (e i) (e k) (e l) a ∈ W ∧ chu1 (e j) (e k) (e l) a ∈ W ∧
        W = Submodule.span ℂ (Set.range ![chu0 (e i) (e k) (e l) a, chu1 (e j) (e k) (e l) a]) := by
  let b := Module.finBasisOfFinrankEq ℂ W hW
  set w0 : Fin 4 → ℂ := (b 0 : Fin 4 → ℂ) with hw0
  set w1 : Fin 4 → ℂ := (b 1 : Fin 4 → ℂ) with hw1
  have hw0W : w0 ∈ W := (b 0).2
  have hw1W : w1 ∈ W := (b 1).2
  have hli : LinearIndependent ℂ ![w0, w1] := by
    have hb : LinearIndependent ℂ ![b 0, b 1] := by
      convert b.linearIndependent using 1; funext n; fin_cases n <;> rfl
    rw [LinearIndependent.pair_iff] at hb ⊢
    intro s t hst
    exact hb s t (Subtype.ext (by simpa [hw0, hw1] using hst))
  let m : Fin 4 → Fin 4 → ℂ := fun i j => w0 i * w1 j - w0 j * w1 i
  have hex : ∃ i j, m i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hw0ne : w0 ≠ 0 := hli.ne_zero 0
    obtain ⟨i, hi⟩ : ∃ i, w0 i ≠ 0 := by
      by_contra h; push Not at h; exact hw0ne (funext h)
    have := LinearIndependent.pair_iff.mp hli (-w1 i) (w0 i) (by
      ext n; have := hcon i n; simp [m] at this ⊢; linear_combination this)
    exact hi this.2
  obtain ⟨⟨i, j⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun ij : Fin 4 × Fin 4 => ‖m ij.1 ij.2‖) Finset.univ_nonempty
  simp only [Finset.mem_univ, true_implies, Prod.forall] at hmax
  set μ := m i j with hμ
  have hμ0 : μ ≠ 0 := by
    obtain ⟨i', j', h'⟩ := hex
    intro h0
    have := hmax i' j'
    rw [h0, norm_zero] at this
    exact h' (norm_le_zero_iff.mp this)
  have hij : i ≠ j := by rintro rfl; apply hμ0; simp [hμ, m]
  obtain ⟨k, l, hik, hil, hjk, hjl, hkl⟩ := exists_compl i j hij
  set u0 : Fin 4 → ℂ := μ⁻¹ • (w1 j • w0 - w0 j • w1) with hu0
  set u1 : Fin 4 → ℂ := μ⁻¹ • (w0 i • w1 - w1 i • w0) with hu1
  have hu0n : ∀ n, u0 n = μ⁻¹ * m n j := by intro n; simp only [hu0, m, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have hu1n : ∀ n, u1 n = μ⁻¹ * m i n := by intro n; simp only [hu1, m, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have hu0W : u0 ∈ W := W.smul_mem _ (W.sub_mem (W.smul_mem _ hw0W) (W.smul_mem _ hw1W))
  have hu1W : u1 ∈ W := W.smul_mem _ (W.sub_mem (W.smul_mem _ hw1W) (W.smul_mem _ hw0W))
  have hmm : ∀ n, m n n = 0 := by intro n; simp only [m]; ring
  have hanti : ∀ n n', m n n' = - m n' n := by intro n n'; simp only [m]; ring
  have hμμ : μ⁻¹ * μ = 1 := inv_mul_cancel₀ hμ0
  have hμμ' : μ⁻¹ * m i j = 1 := hμμ
  let a : Fin 4 → ℂ := ![u0 k, u0 l, u1 k, u1 l]
  have hc0 : chu0 (e i) (e k) (e l) a = u0 := by
    ext n
    rcases fin4_cases i j k l n hij hik hil hjk hjl hkl with h | h | h | h <;> rw [h]
    · simp [chu0, a, Pi.single_apply, hik.symm, hil.symm, hu0n, hμμ']
    · simp [chu0, a, Pi.single_apply, hij.symm, hjk, hjl, hu0n, hmm]
    · simp [chu0, a, Pi.single_apply, hik, hkl]
    · simp [chu0, a, Pi.single_apply, hil, hkl.symm]
  have hc1 : chu1 (e j) (e k) (e l) a = u1 := by
    ext n
    rcases fin4_cases i j k l n hij hik hil hjk hjl hkl with h | h | h | h <;> rw [h]
    · simp [chu1, a, Pi.single_apply, hij, hik.symm, hil.symm, hu1n, hmm]
    · simp [chu1, a, Pi.single_apply, hjk.symm, hjl.symm, hu1n, hμμ']
    · simp [chu1, a, Pi.single_apply, hjk, hkl]
    · simp [chu1, a, Pi.single_apply, hjl, hkl.symm]
  have hbd : ∀ n n', ‖μ⁻¹ * m n n'‖ ≤ 1 := by
    intro n n'
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.mpr hμ0), mul_one]
    exact hmax n n'
  refine ⟨i, j, k, l, ⟨hij, hik, hil, hjk, hjl, hkl⟩, a, ?_, ?_, ?_, ?_⟩
  · rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro n; fin_cases n
    · show ‖u0 k‖ ≤ 1; rw [hu0n]; exact hbd _ _
    · show ‖u0 l‖ ≤ 1; rw [hu0n]; exact hbd _ _
    · show ‖u1 k‖ ≤ 1; rw [hu1n]; exact hbd _ _
    · show ‖u1 l‖ ≤ 1; rw [hu1n]; exact hbd _ _
  · rw [hc0]; exact hu0W
  · rw [hc1]; exact hu1W
  · rw [hc0, hc1]
    have hli2 : LinearIndependent ℂ ![u0, u1] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 := congrFun hst i
      have h2 := congrFun hst j
      simp [hu0n, hu1n, hmm, hμμ'] at h1 h2
      exact ⟨h1, h2⟩
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨n, rfl⟩
      fin_cases n
      · exact hu0W
      · exact hu1W
    · rw [finrank_span_eq_card hli2, hW]; simp

lemma polar3_of_mem (F : MvPolynomial (Fin 4) ℂ) (W : Submodule ℂ (Fin 4 → ℂ))
    (hWF : ∀ x ∈ W, eval x F = 0) (x y z : Fin 4 → ℂ) (hx : x ∈ W) (hy : y ∈ W) (hz : z ∈ W) :
    polar3 F x y z = 0 := by
  simp only [polar3]
  rw [hWF _ (W.add_mem (W.add_mem hx hy) hz), hWF _ (W.add_mem hx hy), hWF _ (W.add_mem hy hz),
    hWF _ (W.add_mem hz hx), hWF _ hx, hWF _ hy, hWF _ hz]
  ring


/-! ### Lines in a chart -/

lemma chart_line (H : MvPolynomial (Fin 4) ℂ) (hH : IsCubicForm H) (i j k l : Fin 4)
    (hd : i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l) (a : Fin 4 → ℂ)
    (h : Φ H (e i) (e j) (e k) (e l) a = 0) :
    Submodule.span ℂ (Set.range ![chu0 (e i) (e k) (e l) a, chu1 (e j) (e k) (e l) a])
      ∈ linesOf H := by
  obtain ⟨hij, hik, hil, hjk, hjl, hkl⟩ := hd
  set u0 := chu0 (e i) (e k) (e l) a
  set u1 := chu1 (e j) (e k) (e l) a
  have hli : LinearIndependent ℂ ![u0, u1] := by
    rw [LinearIndependent.pair_iff]
    intro s r hsr
    have h1 := congrFun hsr i
    have h2 := congrFun hsr j
    simp [u0, u1, chu0, chu1, Pi.single_apply, hij, hik, hil, hjk, hjl, hij.symm, hik.symm,
      hil.symm, hjk.symm, hjl.symm] at h1 h2
    exact ⟨h1, h2⟩
  have h0 : eval u0 H = 0 := by simpa [Φ] using congrFun h 0
  have h1 : polar3 H u0 u0 u1 = 0 := by simpa [Φ] using congrFun h 1
  have h2 : polar3 H u1 u1 u0 = 0 := by simpa [Φ] using congrFun h 2
  have h3 : eval u1 H = 0 := by simpa [Φ] using congrFun h 3
  refine ⟨?_, ?_⟩
  · rw [finrank_span_eq_card hli]; simp
  · intro w hw
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union, Submodule.mem_span_pair] at hw
    obtain ⟨s, r, rfl⟩ := hw
    rw [expST H hH u0 u1 s r, h0, h1, h2, h3]; ring

/-! ### The pencil -/

/-- The base cubic `G = x₂x₀² + x₃x₁²`. -/
noncomputable def G0 : MvPolynomial (Fin 4) ℂ := X 2 * X 0 ^ 2 + X 3 * X 1 ^ 2

lemma G0_cubic : IsCubicForm G0 := by
  unfold IsCubicForm G0
  exact ((isHomogeneous_X ℂ 2).mul ((isHomogeneous_X ℂ 0).pow 2)).add
    ((isHomogeneous_X ℂ 3).mul ((isHomogeneous_X ℂ 1).pow 2))

/-- The pencil `F_t = (1-t) G + t F`. -/
noncomputable def pencil (F : MvPolynomial (Fin 4) ℂ) (t : ℂ) : MvPolynomial (Fin 4) ℂ :=
  C (1 - t) * G0 + C t * F

lemma pencil_cubic (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (t : ℂ) :
    IsCubicForm (pencil F t) :=
  (G0_cubic.C_mul _).add (hF.C_mul _)

lemma Φ_pencil (F : MvPolynomial (Fin 4) ℂ) (t : ℂ) (v0 v1 p q a : Fin 4 → ℂ) :
    Φ (pencil F t) v0 v1 p q a = (1 - t) • Φ G0 v0 v1 p q a + t • Φ F v0 v1 p q a := by
  funext k
  fin_cases k <;> simp [Φ, polar3, pencil] <;> ring

/-! ### Closedness of the set of good parameters -/

lemma isClosed_good (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) :
    IsClosed {t : ℂ | (linesOf (pencil F t)).Nonempty} := by
  let S : Set (Fin 4 × Fin 4 × Fin 4 × Fin 4) := {c | c.1 ≠ c.2.1 ∧ c.1 ≠ c.2.2.1 ∧
    c.1 ≠ c.2.2.2 ∧ c.2.1 ≠ c.2.2.1 ∧ c.2.1 ≠ c.2.2.2 ∧ c.2.2.1 ≠ c.2.2.2}
  let Z : (Fin 4 × Fin 4 × Fin 4 × Fin 4) → Set (ℂ × Metric.closedBall (0 : Fin 4 → ℂ) 1) :=
    fun c => {x | Φ (pencil F x.1) (e c.1) (e c.2.1) (e c.2.2.1) (e c.2.2.2) x.2 = 0}
  have hset : {t : ℂ | (linesOf (pencil F t)).Nonempty} = ⋃ c ∈ S, Prod.fst '' Z c := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · rintro ⟨W, hW⟩
      obtain ⟨i, j, k, l, hd, a, ha, h0, h1, -⟩ := cover W hW.1
      refine ⟨(i, j, k, l), hd, ⟨t, ⟨a, mem_closedBall_zero_iff.2 ha⟩⟩, ?_, rfl⟩
      have hWF := hW.2
      show Φ (pencil F t) (e i) (e j) (e k) (e l) a = 0
      ext n; fin_cases n
      · exact hWF _ h0
      · exact polar3_of_mem _ W hWF _ _ _ h0 h0 h1
      · exact polar3_of_mem _ W hWF _ _ _ h1 h1 h0
      · exact hWF _ h1
    · rintro ⟨⟨i, j, k, l⟩, hd, ⟨t', a⟩, hZ, rfl⟩
      exact ⟨_, chart_line _ (pencil_cubic F hF t') i j k l hd a hZ⟩
  rw [hset]
  refine (Set.toFinite S).isClosed_biUnion (fun c _ => isClosedMap_fst_of_compactSpace _ ?_)
  refine isClosed_eq ?_ continuous_const
  have hc : ∀ H : MvPolynomial (Fin 4) ℂ, Continuous fun x : ℂ × Metric.closedBall (0 : Fin 4 → ℂ) 1 =>
      Φ H (e c.1) (e c.2.1) (e c.2.2.1) (e c.2.2.2) (x.2 : Fin 4 → ℂ) := fun H =>
    (differentiable_Φ H _ _ _ _).continuous.comp (continuous_subtype_val.comp continuous_snd)
  simp only [Φ_pencil]
  exact ((continuous_const.sub continuous_fst).smul (hc G0)).add (continuous_fst.smul (hc F))

/-! ### The chart equations as polynomials in `ℂ[t,a,b,c,d]` -/

abbrev R5 := MvPolynomial (Fin 5) ℂ

noncomputable def U0 : Fin 4 → R5 := ![1, 0, X 1, X 2]
noncomputable def U1 : Fin 4 → R5 := ![0, 1, X 3, X 4]

/-- Substitute a vector of polynomials into `H`. -/
noncomputable def ev (H : MvPolynomial (Fin 4) ℂ) (V : Fin 4 → R5) : R5 := aeval V H

/-- Six times the polarization, at polynomial vectors. -/
noncomputable def pol6 (H : MvPolynomial (Fin 4) ℂ) (V W Z : Fin 4 → R5) : R5 :=
  ev H (V + W + Z) - ev H (V + W) - ev H (W + Z) - ev H (Z + V) + ev H V + ev H W + ev H Z

noncomputable def Ψ (H : MvPolynomial (Fin 4) ℂ) : Fin 4 → R5 :=
  ![ev H U0, pol6 H U0 U0 U1, pol6 H U1 U1 U0, ev H U1]

/-- The four chart equations of the pencil. -/
noncomputable def fk (F : MvPolynomial (Fin 4) ℂ) (k : Fin 4) : R5 :=
  (1 - X 0) * Ψ G0 k + X 0 * Ψ F k

def tl (x : Fin 5 → ℂ) : Fin 4 → ℂ := ![x 1, x 2, x 3, x 4]

noncomputable def evv (x : Fin 5 → ℂ) (V : Fin 4 → R5) : Fin 4 → ℂ := fun i => eval x (V i)

lemma evv_add (x : Fin 5 → ℂ) (V W : Fin 4 → R5) : evv x (V + W) = evv x V + evv x W := by
  funext i; simp [evv]

lemma eval_ev (H : MvPolynomial (Fin 4) ℂ) (V : Fin 4 → R5) (x : Fin 5 → ℂ) :
    eval x (ev H V) = eval (evv x V) H := by
  induction H using MvPolynomial.induction_on with
  | C a => simp [ev]
  | add f g hf hg => simp [ev] at hf hg ⊢; rw [hf, hg]
  | mul_X f i hf => simp [ev] at hf ⊢; rw [hf]; rfl

lemma evv_U0 (x : Fin 5 → ℂ) : evv x U0 = chu0 (e 0) (e 2) (e 3) (tl x) := by
  funext i; fin_cases i <;> simp [evv, U0, chu0, tl, Pi.single_apply]

lemma evv_U1 (x : Fin 5 → ℂ) : evv x U1 = chu1 (e 1) (e 2) (e 3) (tl x) := by
  funext i; fin_cases i <;> simp [evv, U1, chu1, tl, Pi.single_apply]

lemma eval_Ψ (H : MvPolynomial (Fin 4) ℂ) (x : Fin 5 → ℂ) (k : Fin 4) :
    eval x (Ψ H k) = ![1, 6, 6, 1] k * Φ H (e 0) (e 1) (e 2) (e 3) (tl x) k := by
  fin_cases k <;>
    simp [Ψ, pol6, Φ, polar3, eval_ev, evv_add, evv_U0, evv_U1]

lemma eval_fk (F : MvPolynomial (Fin 4) ℂ) (x : Fin 5 → ℂ) (k : Fin 4) :
    eval x (fk F k) = ![1, 6, 6, 1] k * Φ (pencil F (x 0)) (e 0) (e 1) (e 2) (e 3) (tl x) k := by
  rw [Φ_pencil]
  simp only [fk, eval_add, eval_mul, eval_sub, map_one, eval_X, eval_Ψ, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

lemma Ψ_G0 : Ψ G0 = ![X 1, 2 * X 3, 2 * X 2, X 4] := by
  funext k
  fin_cases k <;> simp [Ψ, pol6, ev, G0, U0, U1] <;> ring

/-! ### The ideal identity `(f_k) + (t) = m` -/

noncomputable def m0 : Ideal R5 := vanishingIdeal ℂ {(0 : Fin 5 → ℂ)}

lemma mem_van (f : R5) (x : Fin 5 → ℂ) : f ∈ vanishingIdeal ℂ {x} ↔ eval x f = 0 :=
  mem_vanishingIdeal_singleton_iff _ _

noncomputable def Iset (F : MvPolynomial (Fin 4) ℂ) : Finset R5 := Finset.univ.image (fk F)

lemma Iset_card (F : MvPolynomial (Fin 4) ℂ) : (Iset F).card ≤ 4 :=
  Finset.card_image_le.trans (by simp)

lemma tl_zero : tl 0 = 0 := by funext i; fin_cases i <;> rfl

lemma fk_mem_m0 (F : MvPolynomial (Fin 4) ℂ) (k : Fin 4) : fk F k ∈ m0 := by
  rw [m0, mem_van, eval_fk]
  have : pencil F ((0 : Fin 5 → ℂ) 0) = G0 := by simp [pencil]
  rw [this, tl_zero]
  fin_cases k <;> simp [Φ, polar3, G0, chu0, chu1]

lemma key_sup (F : MvPolynomial (Fin 4) ℂ) :
    Ideal.span (Iset F : Set R5) ⊔ Ideal.span {X 0} = m0 := by
  classical
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw [Ideal.span_le]; intro f hf
      simp only [Iset, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hf
      obtain ⟨k, rfl⟩ := hf; exact fk_mem_m0 F k
    · rw [Ideal.span_singleton_le_iff_mem, m0, mem_vanishingIdeal_singleton_iff]; simp
  · set J := Ideal.span (Iset F : Set R5) ⊔ Ideal.span {X 0}
    have hX0 : (X 0 : R5) ∈ J := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    have hfk : ∀ k, fk F k ∈ J := fun k =>
      Ideal.mem_sup_left (Ideal.subset_span (by simp [Iset]))
    have hΨ : ∀ k, Ψ G0 k ∈ J := by
      intro k
      have : Ψ G0 k = fk F k - X 0 * (Ψ F k - Ψ G0 k) := by simp only [fk]; ring
      rw [this]; exact J.sub_mem (hfk k) (J.mul_mem_right _ hX0)
    have h2 : ∀ p : R5, C (2⁻¹ : ℂ) * (2 * p) = p := by
      intro p; rw [← mul_assoc, ← map_ofNat C 2, ← C_mul]; norm_num
    have hX : ∀ i, (X i : R5) ∈ J := by
      intro i; fin_cases i
      · exact hX0
      · have := hΨ 0; rw [Ψ_G0] at this; simpa using this
      · have := J.mul_mem_left (C (2⁻¹ : ℂ)) (hΨ 2); rw [Ψ_G0] at this
        simp only [Matrix.cons_val_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.vecHead, Matrix.vecTail] at this
        simp only [Function.comp, Fin.succ_zero_eq_one, Matrix.cons_val_one,
          Matrix.cons_val_zero, Matrix.vecHead] at this
        rw [h2] at this; simpa using this
      · have := J.mul_mem_left (C (2⁻¹ : ℂ)) (hΨ 1); rw [Ψ_G0] at this
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
        rw [h2] at this; simpa using this
      · have := hΨ 3; rw [Ψ_G0] at this; simpa using this
    intro f hf
    have hspan : f ∈ Ideal.span ((X : Fin 5 → R5) '' Set.univ) := by
      rw [mem_ideal_span_X_image]
      intro mm hmm
      by_contra hcon
      push Not at hcon
      have h0 : mm = 0 := by ext i; exact hcon i (Set.mem_univ i)
      subst h0
      rw [m0, mem_van] at hf
      rw [mem_support_iff] at hmm
      apply hmm
      rw [← constantCoeff_eq]
      simpa [eval_zero] using hf
    refine (Ideal.span_le.2 ?_) hspan
    rintro _ ⟨i, -, rfl⟩; exact hX i

/-! ### Krull's height theorem step -/

noncomputable def trans (p : Fin 5 → ℂ) : MvPolynomial (Fin 5) ℂ ≃ₐ[ℂ] MvPolynomial (Fin 5) ℂ :=
  AlgEquiv.ofAlgHom (aeval fun i => X i + C (p i)) (aeval fun i => X i - C (p i))
    (by ext i; simp) (by ext i; simp)

lemma eval_trans (p x : Fin 5 → ℂ) (f : MvPolynomial (Fin 5) ℂ) :
    eval x (trans p f) = eval (x + p) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [trans]
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf => rw [map_mul, eval_mul, hf]; simp [trans]

/-- The origin's maximal ideal in `ℂ[x₀,…,x₄]` has height 5. -/
lemma height_origin : (vanishingIdeal ℂ {(0 : Fin 5 → ℂ)}).height = 5 := by
  have h5 : ringKrullDim (MvPolynomial (Fin 5) ℂ) = 5 := by simp
  have : FiniteRingKrullDim (MvPolynomial (Fin 5) ℂ) :=
    finiteRingKrullDim_iff_ne_bot_and_top.2 ⟨by rw [h5]; decide, by rw [h5]; decide⟩
  obtain ⟨M, hM, hht⟩ := Ideal.exists_isMaximal_height (R := MvPolynomial (Fin 5) ℂ)
  obtain ⟨p, rfl⟩ := (isMaximal_iff_eq_vanishingIdeal_singleton).1 hM
  have hmap : Ideal.map (trans p).toRingEquiv (vanishingIdeal ℂ {p}) =
      vanishingIdeal ℂ {(0 : Fin 5 → ℂ)} := by
    ext f
    rw [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨g, hg, rfl⟩
      simp only [mem_vanishingIdeal_singleton_iff] at hg ⊢
      have := eval_trans p 0 g
      simp only [zero_add] at this
      change eval 0 ((trans p) g) = 0
      rw [this]; exact hg
    · intro hf
      refine ⟨(trans p).symm f, ?_, by simp⟩
      simp only [mem_vanishingIdeal_singleton_iff] at hf ⊢
      have := eval_trans p 0 ((trans p).symm f)
      simp only [AlgEquiv.apply_symm_apply, zero_add] at this
      change eval p ((trans p).symm f) = 0
      rw [← this]; exact hf
  rw [← hmap, RingEquiv.height_map]
  rw [h5] at hht
  have : ((vanishingIdeal ℂ {p}).height : WithBot ℕ∞) = ((5 : ℕ∞) : WithBot ℕ∞) := hht
  exact WithBot.coe_injective this

/-- Key Krull step: if `I` is generated by 4 elements, lies in the origin ideal `m`,
and `I ⊔ (X 0) = m`, then `X 0` lies in no minimal prime of `I` below `m`. -/
lemma X0_not_mem (s : Finset (MvPolynomial (Fin 5) ℂ)) (hs : s.card ≤ 4)
    (hm : Ideal.span (s : Set _) ⊔ Ideal.span {X 0} = vanishingIdeal ℂ {(0 : Fin 5 → ℂ)})
    (P : Ideal (MvPolynomial (Fin 5) ℂ)) (hP : P ∈ (Ideal.span (s : Set _)).minimalPrimes)
    (hPm : P ≤ vanishingIdeal ℂ {(0 : Fin 5 → ℂ)}) : X 0 ∉ P := by
  intro hX
  have hle : vanishingIdeal ℂ {(0 : Fin 5 → ℂ)} ≤ P := by
    rw [← hm]; exact sup_le hP.1.2 ((Ideal.span_singleton_le_iff_mem _).2 hX)
  have heq : P = vanishingIdeal ℂ {(0 : Fin 5 → ℂ)} := le_antisymm hPm hle
  have h1 := Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes _ _ hP
  have h2 : (Submodule.spanRank (Ideal.span (s : Set (MvPolynomial (Fin 5) ℂ)))).toENat ≤ 4 := by
    have := Submodule.spanRank_span_le_card (R := MvPolynomial (Fin 5) ℂ)
      ((s : Set (MvPolynomial (Fin 5) ℂ)))
    have h' : Cardinal.toENat (Submodule.spanRank (Ideal.span (s : Set (MvPolynomial (Fin 5) ℂ))))
        ≤ Cardinal.toENat (Cardinal.mk (s : Set (MvPolynomial (Fin 5) ℂ))) :=
      Cardinal.toENat.monotone' this
    simp only [Finset.coe_sort_coe, Cardinal.mk_coe_finset, map_natCast] at h'
    exact h'.trans (by exact_mod_cast hs)
  rw [heq, height_origin] at h1
  have := h1.trans h2
  norm_num at this


/-! ### Flat ⇒ open projection -/

section
variable (P : Ideal R5) [hP : P.IsPrime]

noncomputable def φ : Polynomial ℂ →+* R5 ⧸ P :=
  (Ideal.Quotient.mk P).comp (Polynomial.aeval (X 0 : R5)).toRingHom

noncomputable instance (priority := 100) alg : Algebra (Polynomial ℂ) (R5 ⧸ P) := (φ P).toAlgebra


lemma φ_inj (h : ∀ g : Polynomial ℂ, g ≠ 0 → Polynomial.aeval (X 0 : R5) g ∉ P) :
    Function.Injective (φ P) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  by_contra hne
  exact h g hne (Ideal.Quotient.eq_zero_iff_mem.1 hg)

instance ft : Algebra.FiniteType (Polynomial ℂ) (R5 ⧸ P) := by
  classical
  refine ⟨⟨Finset.univ.image (fun i => Ideal.Quotient.mk P (X i)), ?_⟩⟩
  rw [eq_top_iff]
  rintro y -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction f using MvPolynomial.induction_on with
  | C a =>
    have : Ideal.Quotient.mk P (C a) = algebraMap (Polynomial ℂ) (R5 ⧸ P) (Polynomial.C a) := by
      simp [alg, φ, RingHom.algebraMap_toAlgebra]
    rw [this]; exact Subalgebra.algebraMap_mem _ _
  | add f g hf hg => rw [map_add]; exact Subalgebra.add_mem _ hf hg
  | mul_X f i hf =>
    rw [map_mul]
    exact Subalgebra.mul_mem _ hf (Algebra.subset_adjoin (by simp))

instance fp : Algebra.FinitePresentation (Polynomial ℂ) (R5 ⧸ P) :=
  Algebra.FinitePresentation.of_finiteType.1 inferInstance

lemma flat_of (h : Function.Injective (φ P)) : Module.Flat (Polynomial ℂ) (R5 ⧸ P) := by
  have : Module.IsTorsionFree (Polynomial ℂ) (R5 ⧸ P) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro r m hrm
    rw [Algebra.smul_def, mul_eq_zero] at hrm
    rcases hrm with h' | h'
    · left; exact (injective_iff_map_eq_zero (φ P)).1 h r h'
    · right; exact h'
  infer_instance

end

lemma aeval_X0_eval (g : Polynomial ℂ) (x : Fin 5 → ℂ) :
    eval x (Polynomial.aeval (X 0 : R5) g) = g.eval (x 0) := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

lemma inj_aux (P : Ideal R5) [hP : P.IsPrime] (hX : X 0 ∉ P) (hPm : P ≤ m0) (g : Polynomial ℂ)
    (hg : g ≠ 0) : Polynomial.aeval (X 0 : R5) g ∉ P := by
  obtain ⟨q, hq, hdvd⟩ := g.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hg 0
  rw [hq, map_mul, map_pow]
  intro hmem
  rcases hP.mem_or_mem hmem with h | h
  · simp only [map_zero, sub_zero, Polynomial.aeval_X] at h
    exact hX (hP.mem_of_pow_mem _ h)
  · have := hPm h
    rw [m0, mem_van, aeval_X0_eval] at this
    apply hdvd; rw [Polynomial.dvd_iff_isRoot]; simpa using this

lemma cofinite_good (P : Ideal R5) [hP : P.IsPrime] (hX : X 0 ∉ P) (hPm : P ≤ m0) :
    {c : ℂ | ¬ ∃ x : Fin 5 → ℂ, x 0 = c ∧ ∀ f ∈ P, eval x f = 0}.Finite := by
  have hinj : Function.Injective (φ P) := φ_inj P (fun g hg => inj_aux P hX hPm g hg)
  have : Module.Flat (Polynomial ℂ) (R5 ⧸ P) := flat_of P hinj
  have hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap (Polynomial ℂ) (R5 ⧸ P))) :=
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  set O := Set.range (PrimeSpectrum.comap (algebraMap (Polynomial ℂ) (R5 ⧸ P))) with hOdef
  have hO : IsOpen O := by rw [hOdef, ← Set.image_univ]; exact hopen _ isOpen_univ
  have hne : O.Nonempty := by
    obtain ⟨q⟩ := (inferInstance : Nonempty (PrimeSpectrum (R5 ⧸ P)))
    exact ⟨_, q, rfl⟩
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Oᶜ).1 hO.isClosed_compl
  have hns : ¬ ((J : Set (Polynomial ℂ)) ⊆ (nilradical (Polynomial ℂ) : Set (Polynomial ℂ))) := by
    intro h
    rw [← PrimeSpectrum.zeroLocus_eq_univ_iff, ← hJ] at h
    obtain ⟨z, hz⟩ := hne
    have : z ∈ Oᶜ := h ▸ Set.mem_univ z
    exact this hz
  obtain ⟨g, hgJ, hgn⟩ := Set.not_subset.1 hns
  have hg0 : g ≠ 0 := by rintro rfl; exact hgn (zero_mem _)
  refine (Polynomial.finite_setOfPred_isRoot hg0).subset ?_
  intro c hc
  simp only [Set.mem_ofPred_eq] at hc ⊢
  by_contra hroot
  apply hc
  have hprime : (Ideal.span {Polynomial.X - Polynomial.C c}).IsPrime :=
    (Ideal.span_singleton_prime (Polynomial.X_sub_C_ne_zero c)).2 (Polynomial.prime_X_sub_C c)
  let pt : PrimeSpectrum (Polynomial ℂ) := ⟨_, hprime⟩
  have hpt : pt ∈ O := by
    by_contra hn
    have h1 : pt ∈ PrimeSpectrum.zeroLocus (J : Set (Polynomial ℂ)) := hJ ▸ hn
    have h2 : g ∈ pt.asIdeal := h1 hgJ
    rw [Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot] at h2
    exact hroot h2
  obtain ⟨Q, hQ⟩ := hpt
  have hQc : Ideal.Quotient.mk P (X 0 - C c) ∈ Q.asIdeal := by
    have h1 : Polynomial.X - Polynomial.C c ∈
        (PrimeSpectrum.comap (algebraMap (Polynomial ℂ) (R5 ⧸ P)) Q).asIdeal := by
      rw [hQ]; exact Ideal.mem_span_singleton_self _
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h1
    convert h1 using 1
    simp [RingHom.algebraMap_toAlgebra, φ]
  set Q' := Q.asIdeal.comap (Ideal.Quotient.mk P)
  obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal Q' (Ideal.IsPrime.ne_top inferInstance)
  obtain ⟨x, rfl⟩ := isMaximal_iff_eq_vanishingIdeal_singleton.1 hM
  refine ⟨x, ?_, ?_⟩
  · have := hQM (show X 0 - C c ∈ Q' from hQc)
    rw [mem_van] at this
    simpa [sub_eq_zero] using this
  · intro f hf
    have : f ∈ Q' := by
      show Ideal.Quotient.mk P f ∈ Q.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hf]; exact zero_mem _
    exact (mem_van _ _).1 (hQM this)

end ELAux

open CubicSurface27 ELAux in
theorem solution (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) :
    (linesOf F).Nonempty := by
  have hm : (m0).IsPrime :=
    (isMaximal_iff_eq_vanishingIdeal_singleton.2 ⟨0, rfl⟩).isPrime
  have hle : Ideal.span (Iset F : Set R5) ≤ m0 := key_sup F ▸ le_sup_left
  obtain ⟨P, hPmin, hPm⟩ := Ideal.exists_minimalPrimes_le hle
  have : P.IsPrime := hPmin.1.1
  have hX : (X 0 : R5) ∉ P := X0_not_mem (Iset F) (Iset_card F) (key_sup F) P hPmin hPm
  have hfin := cofinite_good P hX hPm
  set T := {t : ℂ | (linesOf (pencil F t)).Nonempty}
  have hsub : {c : ℂ | ¬ ∃ x : Fin 5 → ℂ, x 0 = c ∧ ∀ f ∈ P, eval x f = 0}ᶜ ⊆ T := by
    intro c hc
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] at hc
    obtain ⟨x, rfl, hx⟩ := hc
    have hz : Φ (pencil F (x 0)) (e 0) (e 1) (e 2) (e 3) (tl x) = 0 := by
      funext k
      have h1 := hx (fk F k) (hPmin.1.2 (Ideal.subset_span (by simp [Iset])))
      rw [eval_fk] at h1
      have h6 : (![1, 6, 6, 1] : Fin 4 → ℂ) k ≠ 0 := by fin_cases k <;> norm_num
      simpa [h6] using h1
    exact ⟨_, chart_line _ (pencil_cubic F hF _) 0 1 2 3 (by decide) _ hz⟩
  have hdense : Dense T := (hfin.countable.dense_compl ℂ).mono hsub
  have hcl : IsClosed T := isClosed_good F hF
  have hT : T = Set.univ := by rw [← hcl.closure_eq, hdense.closure_eq]
  have h1 : (1 : ℂ) ∈ T := hT ▸ Set.mem_univ _
  simpa [T, pencil] using h1
