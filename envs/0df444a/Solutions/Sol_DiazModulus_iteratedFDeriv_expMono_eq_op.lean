-- Prove2me | solution 1 for DiazModulus.iteratedFDeriv_expMono_eq_op
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:21:17.971988+00:00
-- url     : https://prove2.me/submissions/a1a3341a-7dfc-4d9a-9ceb-d49d0ea4968f

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Iterated derivatives of `z^τ e^{⟨t, z⟩}` as `Op⋯Op X^τ`

For a polynomial `f` in the first block of variables put `G_f(z) = f(z.1) · e^{Λ(z)}`, where
`Λ(z) = Σ_i t_i z.2_i` is a continuous linear form. For `v = (v₁, v₂)` let
`Op_v = Σ_h v₁(h) ∂_h + Λ(v)`. The product rule (`HasFDerivAt.mul`, `HasFDerivAt.cexp`) and the
derivative of polynomial evaluation, `D(f ∘ fst)(z) v = Σ_h ∂_h f(z.1) v₁(h)` (proved by
`MvPolynomial.induction_on`), give `DG_f(z) v = G_{Op_v f}(z)`.
Then we induct on `r` for all `f` at once: `iteratedFDeriv_succ_apply_right` writes the
`(r+1)`-st derivative as the `r`-th derivative of `fderiv G_f`, evaluated at the last direction;
evaluation at a fixed vector is a continuous linear map, and it commutes with `iteratedFDeriv`
(`ContinuousLinearMap.iteratedFDeriv_comp_left`, since `G_f` is smooth), so we get the
`r`-th derivative of `G_{Op_{m_last} f}`. The list product applies its last factor first
(`List.ofFn_succ'`), which matches. With `f = ∏_h X_h^{τ_h}` this is the statement. -/

namespace C14_A6
open DiazModulus MvPolynomial

set_option linter.unusedSectionVars false

variable {ι₀ ι₁ : Type} [Fintype ι₀] [Fintype ι₁] [DecidableEq ι₀]

/-- The operator `Op_v`. -/
noncomputable def Op (tc : ι₁ → ℂ) (v : (ι₀ → ℂ) × (ι₁ → ℂ)) : Module.End ℂ (MvPolynomial ι₀ ℂ) :=
  ∑ h, v.1 h • (MvPolynomial.pderiv h).toLinearMap + (∑ i, v.2 i * tc i) • LinearMap.id

/-- The linear form `Λ`. -/
noncomputable def Lam (tc : ι₁ → ℂ) : ((ι₀ → ℂ) × (ι₁ → ℂ)) →L[ℂ] ℂ :=
  ∑ i, tc i • (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ (ι₀ → ℂ) (ι₁ → ℂ))

lemma Lam_apply (tc : ι₁ → ℂ) (z : (ι₀ → ℂ) × (ι₁ → ℂ)) :
    Lam tc z = ∑ i, tc i * z.2 i := by
  simp [Lam]

/-- The function `G_f`. -/
noncomputable def G (tc : ι₁ → ℂ) (f : MvPolynomial ι₀ ℂ) (z : (ι₀ → ℂ) × (ι₁ → ℂ)) : ℂ :=
  eval z.1 f * Complex.exp (Lam tc z)

/-- The coordinate `z ↦ z.1 n`. -/
noncomputable def coord (n : ι₀) : ((ι₀ → ℂ) × (ι₁ → ℂ)) →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj n).comp (ContinuousLinearMap.fst ℂ (ι₀ → ℂ) (ι₁ → ℂ))

lemma hasFDerivAt_eval (f : MvPolynomial ι₀ ℂ) (z : (ι₀ → ℂ) × (ι₁ → ℂ)) :
    HasFDerivAt (fun z : (ι₀ → ℂ) × (ι₁ → ℂ) => eval z.1 f)
      (∑ h, eval z.1 (pderiv h f) • (coord (ι₁ := ι₁) h)) z := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero]
    refine (hasFDerivAt_const (𝕜 := ℂ) a z).congr_fderiv ?_
    exact ContinuousLinearMap.ext fun v => by simp
  | add p q hp hq =>
    simp only [map_add]
    refine (hp.add hq).congr_fderiv ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun h _ => (add_smul _ _ _).symm
  | mul_X p n hp =>
    have hX : HasFDerivAt (fun z : (ι₀ → ℂ) × (ι₁ → ℂ) => z.1 n) (coord (ι₁ := ι₁) n) z :=
      (coord n).hasFDerivAt
    rw [show (fun z : (ι₀ → ℂ) × (ι₁ → ℂ) => eval z.1 (p * X n)) =
        fun z => eval z.1 p * z.1 n from by funext y; simp]
    refine (hp.mul hX).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp [coord, Derivation.leibniz, Pi.single_apply, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum, apply_ite, mul_comm, mul_left_comm]

lemma contDiff_G (tc : ι₁ → ℂ) (f : MvPolynomial ι₀ ℂ) {n : WithTop ℕ∞} :
    ContDiff ℂ n (G tc f) := by
  have he : ContDiff ℂ n (fun z : (ι₀ → ℂ) × (ι₁ → ℂ) => eval z.1 f) := by
    induction f using MvPolynomial.induction_on with
    | C a => simpa using contDiff_const
    | add p q hp hq => simpa [map_add] using hp.add hq
    | mul_X p n' hp =>
      rw [show (fun z : (ι₀ → ℂ) × (ι₁ → ℂ) => eval z.1 (p * X n')) =
          fun z => eval z.1 p * coord (ι₁ := ι₁) n' z from by funext y; simp [coord]]
      exact hp.mul (by exact (coord (ι₁ := ι₁) n').contDiff)
  show ContDiff ℂ n (fun z => eval z.1 f * Complex.exp (Lam tc z))
  exact he.mul (ContDiff.cexp (by exact (Lam (ι₀ := ι₀) tc).contDiff))

lemma fderiv_G_apply (tc : ι₁ → ℂ) (f : MvPolynomial ι₀ ℂ) (v : (ι₀ → ℂ) × (ι₁ → ℂ)) :
    (fun y => fderiv ℂ (G tc f) y v) = G tc (Op tc v f) := by
  funext z
  have hd : HasFDerivAt (G tc f) _ z :=
    (hasFDerivAt_eval (ι₁ := ι₁) f z).mul (Lam tc).hasFDerivAt.cexp
  rw [hd.fderiv]
  simp only [G, Op, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, smul_eq_mul, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.id_apply, Derivation.coeFn_coe,
    map_add, map_sum, smul_eval, coord, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_smul',
    Pi.smul_apply]
  simp only [Lam_apply tc v, Finset.mul_sum, Finset.sum_mul, add_mul]
  rw [add_comm]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring

lemma key (tc : ι₁ → ℂ) (p : (ι₀ → ℂ) × (ι₁ → ℂ)) :
    ∀ (r : ℕ) (m : Fin r → (ι₀ → ℂ) × (ι₁ → ℂ)) (f : MvPolynomial ι₀ ℂ),
      iteratedFDeriv ℂ r (G tc f) p m = G tc ((List.ofFn fun k => Op tc (m k)).prod f) p := by
  intro r
  induction r with
  | zero => intro m f; simp
  | succ r ih =>
    intro m f
    rw [iteratedFDeriv_succ_apply_right]
    have hcomp := (ContinuousLinearMap.apply ℂ ℂ (m (Fin.last r))).iteratedFDeriv_comp_left
      (f := fun y => fderiv ℂ (G tc f) y) (x := p) (n := ⊤)
      (((contDiff_G tc f).fderiv_right (m := ⊤) le_rfl).contDiffAt) (i := r) (by exact_mod_cast le_top)
    have h2 : (iteratedFDeriv ℂ r (fun y => fderiv ℂ (G tc f) y) p (Fin.init m)) (m (Fin.last r))
        = iteratedFDeriv ℂ r ((ContinuousLinearMap.apply ℂ ℂ (m (Fin.last r))) ∘
            fun y => fderiv ℂ (G tc f) y) p (Fin.init m) := by
      rw [hcomp]; rfl
    rw [h2]
    have h3 : ((ContinuousLinearMap.apply ℂ ℂ (m (Fin.last r))) ∘ fun y => fderiv ℂ (G tc f) y)
        = G tc (Op tc (m (Fin.last r)) f) := by
      rw [← fderiv_G_apply]; rfl
    rw [h3, ih, List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton,
      Module.End.mul_apply]
    rfl

end C14_A6

open DiazModulus C14_A6 in
theorem solution {ι₀ ι₁ κ₀ : Type} [Fintype ι₀] [Fintype ι₁] [DecidableEq ι₀]
    (w : κ₀ → (ι₀ → ℂ) × (ι₁ → ℂ)) (τ : ι₀ → ℕ) (t : ι₁ → ℤ) (p : (ι₀ → ℂ) × (ι₁ → ℂ))
    (r : ℕ) (κ : Fin r → κ₀) :
    iteratedFDeriv ℂ r (fun z : (ι₀ → ℂ) × (ι₁ → ℂ) =>
        (∏ h, z.1 h ^ τ h) * Complex.exp (∑ i, (t i : ℂ) * z.2 i)) p (fun k => w (κ k)) =
      MvPolynomial.eval p.1 ((List.ofFn fun k : Fin r =>
            ((∑ h, (w (κ k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w (κ k)).2 i * (t i : ℂ)) • LinearMap.id :
                Module.End ℂ (MvPolynomial ι₀ ℂ)))).prod
          (∏ h, MvPolynomial.X h ^ τ h)) * Complex.exp (∑ i, (t i : ℂ) * p.2 i) := by
  have hfun : (fun z : (ι₀ → ℂ) × (ι₁ → ℂ) =>
        (∏ h, z.1 h ^ τ h) * Complex.exp (∑ i, (t i : ℂ) * z.2 i)) =
      G (fun i => (t i : ℂ)) (∏ h, MvPolynomial.X h ^ τ h) := by
    funext z; simp [G, Lam_apply]
  rw [hfun, key (fun i => (t i : ℂ)) p r (fun k => w (κ k)), G, Lam_apply]
  rfl
