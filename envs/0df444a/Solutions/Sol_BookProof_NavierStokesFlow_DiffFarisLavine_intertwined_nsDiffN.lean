-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiffFarisLavine.intertwined_nsDiffN
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:55:06.290885+00:00
-- url     : https://prove2.me/submissions/e621b23f-674c-4157-9ba7-8afbbd539e00

-- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDiffFarisLavine.lean
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 4000000
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.DiffFarisLavine
open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine
open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.DifferentialL2

private theorem other_momPoly_apply (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :
    momPoly i p = C (-Complex.I) * (pderiv i p - C (1/2 : ℂ) * (X i * p)) := rfl
private theorem other_crePoly_apply (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :
    crePoly i p = X i * p - pderiv i p := rfl
private theorem other_annPoly_apply (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :
    annPoly i p = pderiv i p := rfl
private theorem other_mulXPoly_apply (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :
    mulXPoly i p = X i * p := rfl

private theorem oscPoly_eq (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :
    momPoly i (momPoly i p) + mulXPoly i (mulXPoly i (((1 / 4 : ℂ)) • p))
      = crePoly i (annPoly i p) + ((1 / 2 : ℂ)) • p := by
  have hL : pderiv i (X i * p) = p + X i * pderiv i p := by
    rw [Derivation.leibniz, pderiv_X_self]
    simp [smul_eq_mul]
    ring
  have hd : pderiv i (momPoly i p)
      = C (-Complex.I) * (pderiv i (pderiv i p) - C (1 / 2 : ℂ) * (p + X i * pderiv i p)) := by
    rw [other_momPoly_apply, MvPolynomial.pderiv_C_mul, map_sub, MvPolynomial.pderiv_C_mul, hL]
  have hII : (C (-Complex.I) : MvPolynomial (Fin 3) ℂ) * C (-Complex.I) = -1 := by
    rw [← map_mul]
    norm_num
  have hhalf : (C (1 / 2 : ℂ) : MvPolynomial (Fin 3) ℂ) * C (1 / 2 : ℂ) = C (1 / 4 : ℂ) := by
    rw [← map_mul]
    norm_num
  have hone : (C (1 / 2 : ℂ) : MvPolynomial (Fin 3) ℂ) + C (1 / 2 : ℂ) = 1 := by
    rw [← map_add]
    norm_num
  have hexp : momPoly i (momPoly i p)
      = -(pderiv i (pderiv i p)) + C (1 / 2 : ℂ) * p + X i * pderiv i p
        - C (1 / 4 : ℂ) * (X i * (X i * p)) := by
    conv_lhs => rw [other_momPoly_apply]
    rw [hd]
    conv_lhs => rw [other_momPoly_apply]
    have hfac : C (-Complex.I) * (C (-Complex.I)
          * (pderiv i (pderiv i p) - C (1 / 2 : ℂ) * (p + X i * pderiv i p))
        - C (1 / 2 : ℂ) * (X i * (C (-Complex.I)
          * (pderiv i p - C (1 / 2 : ℂ) * (X i * p)))))
        = (C (-Complex.I) * C (-Complex.I))
          * ((pderiv i (pderiv i p) - C (1 / 2 : ℂ) * (p + X i * pderiv i p))
            - C (1 / 2 : ℂ) * (X i * (pderiv i p - C (1 / 2 : ℂ) * (X i * p)))) := by
      ring
    rw [hfac, hII]
    linear_combination (X i * pderiv i p) * hone - (X i * (X i * p)) * hhalf
  rw [hexp]
  simp only [other_crePoly_apply, other_annPoly_apply, other_mulXPoly_apply, MvPolynomial.smul_eq_C_mul]
  ring

private theorem other_coreOp_coreEquiv (T : MvPolynomial (Fin 3) ℂ →ₗ[ℂ] MvPolynomial (Fin 3) ℂ)
    (p : MvPolynomial (Fin 3) ℂ) : coreOp T (coreEquiv p) = coreEquiv (T p) := by
  simp [coreOp]

private theorem oscOp_eq_number (i : Fin 3) :
    oscOp i = (creOp i).comp (annOp i) + ((1 / 2 : ℂ)) • LinearMap.id := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨p, rfl⟩ := (coreEquiv (d := 3)).surjective y
  simp only [oscOp, momOp, posOp, annOp, creOp, other_coreOp_coreEquiv, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, ← map_add, ← map_smul]
  congr 1
  exact oscPoly_eq i p

theorem BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffN_eq_ladder (mu : ℝ) :
    nsDiffN mu = (((2 * mu : ℝ) : ℂ)) • (∑ i, (creOp i).comp (annOp i))
      + (((3 * mu + 1 : ℝ) : ℂ)) • LinearMap.id := by
  have hsum : (∑ i, oscOp i)
      = (∑ i, (creOp i).comp (annOp i)) + ((3 / 2 : ℂ)) • LinearMap.id := by
    rw [Finset.sum_congr rfl (fun i _ => oscOp_eq_number i), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    match_scalars
    norm_num
  rw [nsDiffN, hsum]
  match_scalars <;> ring


noncomputable section
namespace BookProof.NavierStokesFlow.CanonicalVector
open LpNat FarisLavine IkebeKato ThreeComponent ShiftHamiltonian SignedShift
@[simp] theorem lower_raise (i : Fin 3) (β : Vel) : lower i (raise i β) = β := by
  funext j
  by_cases hji : j = i
  · subst hji; rw [lower_self, raise_self]; omega
  · rw [lower_of_ne hji, raise_of_ne hji]

@[simp] theorem crd_ann (i : Fin 3) (x : lpFiniteModes Vel) :
    crd (ann i x) = aFun i (crd x) := rfl

@[simp] theorem crd_cre (i : Fin 3) (x : lpFiniteModes Vel) :
    crd (cre i x) = cFun i (crd x) := rfl

@[simp] theorem crd_add (x y : lpFiniteModes Vel) : crd (x + y) = crd x + crd y := by
  funext β; simp [crd]

@[simp] theorem crd_smul (a : ℂ) (x : lpFiniteModes Vel) : crd (a • x) = a • crd x := by
  funext β; simp [crd]

@[simp] theorem crd_sub (x y : lpFiniteModes Vel) : crd (x - y) = crd x - crd y := by
  funext β; simp [crd]

theorem crd_injective : Function.Injective crd := by
  intro x y h
  exact Subtype.ext (lp.ext h)

end BookProof.NavierStokesFlow.CanonicalVector
namespace BookProof.HermiteProductBasis
open scoped ENNReal
open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore
open BookProof.HermiteCore
variable {d : ℕ}
@[simp] theorem hermiteMvBasis_apply (a : Fin d →₀ ℕ) :
    hermiteMvBasis a = hermiteMvLp (d := d) a := by
  rw [hermiteMvBasis, HilbertBasis.coe_mk]

theorem pderiv_aeval_self (i : Fin d) (q : Polynomial ℂ) :
    pderiv i (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) q)
      = Polynomial.aeval (X i) (Polynomial.derivative q) := by
  induction q using Polynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n c ih =>
      simp only [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow, map_mul,
        Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
      rw [Derivation.leibniz]
      simp [mul_comm, mul_assoc, algebraMap_eq]

theorem pderiv_aeval_other {i j : Fin d} (h : j ≠ i) (q : Polynomial ℂ) :
    pderiv j (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) q) = 0 := by
  induction q using Polynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n c ih =>
      simp only [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
      rw [Derivation.leibniz]
      simp [h, algebraMap_eq]

theorem pderiv_hermiteFactor_self (i : Fin d) (n : ℕ) :
    pderiv i (hermiteFactor i n) = (n : ℂ) • hermiteFactor i (n - 1) := by
  cases n with
  | zero => simp [hermiteFactor, hermiteCx_zero]
  | succ m =>
      rw [hermiteFactor, pderiv_aeval_self]
      have h : Polynomial.derivative (hermiteCx (m + 1)) = ((m : ℂ) + 1) • hermiteCx m := by
        have hm := congrArg (Polynomial.map (Int.castRingHom ℂ)) (derivative_hermiteZ m)
        simpa [hermiteCx, Polynomial.derivative_map, Polynomial.smul_eq_C_mul,
          Polynomial.map_mul] using hm
      rw [h]
      simp [hermiteFactor, map_smul]

theorem pderiv_hermiteFactor_other {i j : Fin d} (h : j ≠ i) (n : ℕ) :
    pderiv j (hermiteFactor i n) = 0 := pderiv_aeval_other h _

theorem pderiv_hermiteMv (i : Fin d) (a : Fin d →₀ ℕ) :
    pderiv i (hermiteMv a) = ((a i : ℂ)) • hermiteMv (a - Finsupp.single i 1) := by
  classical
  have hrest : ∀ b : Fin d →₀ ℕ, (∀ j : Fin d, j ≠ i → b j = a j) →
      ∏ j ∈ Finset.univ.erase i, hermiteFactor j (b j)
        = ∏ j ∈ Finset.univ.erase i, hermiteFactor j (a j) :=
    fun b hb => Finset.prod_congr rfl fun j hj => by rw [hb j (Finset.ne_of_mem_erase hj)]
  have hsub : ∀ j : Fin d, j ≠ i → (a - Finsupp.single i 1 : Fin d →₀ ℕ) j = a j := by
    intro j hj; simp [Finsupp.tsub_apply, hj]
  have hsi : (a - Finsupp.single i 1 : Fin d →₀ ℕ) i = a i - 1 := by simp [Finsupp.tsub_apply]
  have hzero : pderiv i (∏ j ∈ Finset.univ.erase i, hermiteFactor j (a j)) = 0 := by
    refine Finset.prod_induction _ (fun p => pderiv i p = 0) ?_ (by simp) ?_
    · intro p q hp hq
      rw [Derivation.leibniz, hp, hq]; simp
    · intro j hj
      exact pderiv_aeval_other (Finset.ne_of_mem_erase hj).symm _
  rw [hermiteMv_erase i a, hermiteMv_erase i (a - Finsupp.single i 1), hrest _ hsub, hsi,
    Derivation.leibniz, hzero, pderiv_hermiteFactor_self]
  simp [mul_comm]

@[simp] theorem annPoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    annPoly i p = pderiv i p := rfl

@[simp] theorem crePoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    crePoly i p = X i * p - pderiv i p := rfl

theorem crePoly_hermiteMv (i : Fin d) (a : Fin d →₀ ℕ) :
    crePoly i (hermiteMv a) = hermiteMv (a + Finsupp.single i 1) := by
  rw [crePoly_apply, hermiteMv_X_mul, pderiv_hermiteMv]
  abel

theorem hermiteNorm_succ (n : ℕ) :
    hermiteNorm (n + 1) = hermiteNorm n * Real.sqrt ((n : ℝ) + 1) := by
  have hfac : ((n + 1).factorial : ℝ) * Real.sqrt (2 * Real.pi)
      = ((n : ℝ) + 1) * ((n.factorial : ℝ) * Real.sqrt (2 * Real.pi)) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hermiteNorm, hermiteNorm, hfac, Real.sqrt_mul (by positivity), mul_comm]

theorem hermiteMvNorm_add_single (i : Fin d) (a : Fin d →₀ ℕ) :
    hermiteMvNorm (a + Finsupp.single i 1) = hermiteMvNorm a * Real.sqrt ((a i : ℝ) + 1) := by
  classical
  have hsplit : ∀ b : Fin d →₀ ℕ, hermiteMvNorm b
      = hermiteNorm (b i) * ∏ j ∈ Finset.univ.erase i, hermiteNorm (b j) := by
    intro b
    rw [hermiteMvNorm, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hrest : ∏ j ∈ Finset.univ.erase i, hermiteNorm ((a + Finsupp.single i 1 : Fin d →₀ ℕ) j)
      = ∏ j ∈ Finset.univ.erase i, hermiteNorm (a j) :=
    Finset.prod_congr rfl fun j hj => by
      rw [show (a + Finsupp.single i 1 : Fin d →₀ ℕ) j = a j by
        simp [Finset.ne_of_mem_erase hj]]
  have hai : (a + Finsupp.single i 1 : Fin d →₀ ℕ) i = a i + 1 := by simp
  rw [hsplit (a + Finsupp.single i 1), hrest, hai, hermiteNorm_succ, hsplit a]
  ring

theorem hermiteMvNorm_sub_single {i : Fin d} {a : Fin d →₀ ℕ} (h : 1 ≤ a i) :
    hermiteMvNorm a = hermiteMvNorm (a - Finsupp.single i 1) * Real.sqrt ((a i : ℝ)) := by
  classical
  have hb : a = (a - Finsupp.single i 1) + Finsupp.single i 1 := by
    ext j
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [hj]
  have hbi : ((a - Finsupp.single i 1 : Fin d →₀ ℕ) i : ℝ) + 1 = (a i : ℝ) := by
    rw [show (a - Finsupp.single i 1 : Fin d →₀ ℕ) i = a i - 1 by simp [Finsupp.tsub_apply]]
    have : ((a i - 1 : ℕ) : ℝ) = (a i : ℝ) - 1 := by
      push_cast [Nat.cast_sub h]
      ring
    rw [this]
    ring
  calc hermiteMvNorm a
      = hermiteMvNorm ((a - Finsupp.single i 1) + Finsupp.single i 1) := by rw [← hb]
    _ = hermiteMvNorm (a - Finsupp.single i 1)
          * Real.sqrt (((a - Finsupp.single i 1 : Fin d →₀ ℕ) i : ℝ) + 1) :=
        hermiteMvNorm_add_single i _
    _ = hermiteMvNorm (a - Finsupp.single i 1) * Real.sqrt ((a i : ℝ)) := by rw [hbi]

theorem pgMap_apply (p : MvPolynomial (Fin d) ℂ) : pgMap p = pgLp p := rfl

theorem crePoly_hermiteMvLp (i : Fin d) (a : Fin d →₀ ℕ) :
    ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • pgLp (crePoly i (hermiteMv a))
      = ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ) • hermiteMvLp (a + Finsupp.single i 1) := by
  rw [crePoly_hermiteMv, pgLp_hermiteMv_eq (a + Finsupp.single i 1), smul_smul,
    hermiteMvNorm_add_single]
  congr 1
  have hne : ((hermiteMvNorm a : ℝ) : ℂ) ≠ 0 := hermiteMvNorm_ne_zero a
  push_cast
  field_simp

theorem annPoly_hermiteMvLp (i : Fin d) (a : Fin d →₀ ℕ) :
    ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • pgLp (annPoly i (hermiteMv a))
      = ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ) • hermiteMvLp (a - Finsupp.single i 1) := by
  rw [annPoly_apply, pderiv_hermiteMv, ← pgMap_apply, map_smul, pgMap_apply,
    pgLp_hermiteMv_eq (a - Finsupp.single i 1), smul_smul, smul_smul]
  rcases Nat.eq_zero_or_pos (a i) with h0 | hpos
  · rw [h0]
    simp
  · congr 1
    have hnorm := hermiteMvNorm_sub_single (i := i) (a := a) hpos
    have hsub_pos := hermiteMvNorm_pos (a - Finsupp.single i 1)
    have hai : (0 : ℝ) < (a i : ℝ) := by exact_mod_cast hpos
    have hsqrt_pos : 0 < Real.sqrt ((a i : ℝ)) := Real.sqrt_pos.mpr hai
    have hsqrt : Real.sqrt ((a i : ℝ)) * Real.sqrt ((a i : ℝ)) = (a i : ℝ) :=
      Real.mul_self_sqrt hai.le
    have hreal : (hermiteMvNorm a)⁻¹ * ((a i : ℝ) * hermiteMvNorm (a - Finsupp.single i 1))
        = Real.sqrt ((a i : ℝ)) := by
      rw [hnorm]
      field_simp
      nlinarith [hsqrt, hsub_pos, hsqrt_pos]
    have := congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) hreal
    push_cast at this ⊢
    linear_combination this
end BookProof.HermiteProductBasis
namespace BookProof.NavierStokesFlow.DifferentialL2
open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.LagrangianEsa
variable {d : ℕ}
@[simp] theorem momPoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momPoly i p = C (-Complex.I) * (pderiv i p - C (1/2 : ℂ) * (X i * p)) := rfl

@[simp] theorem mulXPoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    mulXPoly i p = X i * p := rfl

theorem coreEquiv_coe (p : MvPolynomial (Fin d) ℂ) :
    ((coreEquiv p : polyGaussCore (d := d)) : L2d d) = pgLp p := rfl

theorem coreOp_coreEquiv (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (p : MvPolynomial (Fin d) ℂ) : coreOp T (coreEquiv p) = coreEquiv (T p) := by
  simp [coreOp]

theorem coreOp_coe (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (p : MvPolynomial (Fin d) ℂ) :
    ((coreOp T (coreEquiv p) : polyGaussCore (d := d)) : L2d d) = pgLp (T p) := by
  rw [coreOp_coreEquiv, coreEquiv_coe]

@[simp] theorem velIdx_apply (b : Vel) (i : Fin 3) : velIdx b i = b i := rfl

theorem velIdx_raise (i : Fin 3) (b : Vel) :
    velIdx (raise i b) = velIdx b + Finsupp.single i 1 := by
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [raise_of_ne hj, Ne.symm hj]

theorem velIdx_lower (i : Fin 3) (b : Vel) :
    velIdx (lower i b) = velIdx b - Finsupp.single i 1 := by
  ext j
  by_cases hj : j = i
  · subst hj; simp [Finsupp.tsub_apply]
  · simp [lower_of_ne hj, Finsupp.tsub_apply, Ne.symm hj]

theorem core_ext {M : Type*} [AddCommGroup M] [Module ℂ M]
    {F G : lpFiniteModes Vel →ₗ[ℂ] M} (h : ∀ b, F (coreState b) = G (coreState b)) : F = G := by
  refine LinearMap.ext fun x => ?_
  have hx : x ∈ Submodule.span ℂ (Set.range coreState) := by rw [span_coreState]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨b, rfl⟩ := hy; exact h b
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | smul a y _ hy => rw [map_smul, map_smul, hy]

theorem crd_coreState (b g : Vel) : crd (coreState b) g = if g = b then 1 else 0 := by
  simp [crd, coreState, lp.single_apply, Pi.single_apply]

theorem ann_coreState (i : Fin 3) (b : Vel) :
    ann i (coreState b) = ((Real.sqrt ((b i : ℝ)) : ℝ) : ℂ) • coreState (lower i b) := by
  refine crd_injective (funext fun g => ?_)
  rw [crd_ann, crd_smul]
  simp only [aFun, crd_coreState, Pi.smul_apply, smul_eq_mul]
  by_cases hg : raise i g = b
  · have hbi : b i = g i + 1 := by rw [← hg, raise_self]
    have hlow : lower i b = g := by rw [← hg, lower_raise]
    rw [if_pos hg, hlow, if_pos rfl, hbi]
    push_cast
    ring
  · rw [if_neg hg, mul_zero]
    by_cases hg2 : g = lower i b
    · have hb0 : b i = 0 := by
        by_contra hne
        exact hg (by rw [hg2, raise_lower i (Nat.one_le_iff_ne_zero.mpr hne)])
      rw [hb0]
      simp
    · rw [if_neg hg2, mul_zero]

theorem cre_coreState (i : Fin 3) (b : Vel) :
    cre i (coreState b) = ((Real.sqrt ((b i : ℝ) + 1) : ℝ) : ℂ) • coreState (raise i b) := by
  refine crd_injective (funext fun g => ?_)
  rw [crd_cre, crd_smul]
  simp only [cFun, crd_coreState, Pi.smul_apply, smul_eq_mul]
  by_cases hg : g = raise i b
  · have hlow : lower i g = b := by rw [hg, lower_raise]
    have hgi : (g i : ℝ) = (b i : ℝ) + 1 := by rw [hg, raise_self]; push_cast; ring
    rw [hlow, if_pos rfl, if_pos hg, hgi]
  · rw [if_neg hg, mul_zero]
    by_cases hg2 : lower i g = b
    · have hgi : g i = 0 := by
        by_contra hne
        exact hg (by rw [← hg2, raise_lower i (Nat.one_le_iff_ne_zero.mpr hne)])
      rw [hgi]
      simp
    · rw [if_neg hg2, mul_zero]

theorem pgLp_smul (c : ℂ) (p : MvPolynomial (Fin d) ℂ) : pgLp (c • p) = c • pgLp p :=
  map_smul (pgMap (d := d)) c p

@[simp] theorem embedCore_coe (x : lpFiniteModes Vel) :
    ((embedCore x : polyGaussCore (d := 3)) : L2d 3) = velUnitary ((x : L2I Vel)) := rfl

theorem embedCore_coreState (b : Vel) :
    embedCore (coreState b)
      = coreEquiv (((hermiteMvNorm (velIdx b) : ℝ) : ℂ)⁻¹ • hermiteMv (velIdx b)) := by
  refine Subtype.ext ?_
  rw [coreEquiv_coe, embedCore_coe, coreState_coe, velUnitary_single, hermiteVel, hermiteMvLp,
    pgLp_smul]

theorem intertwine_ann (i : Fin 3) : (annOp i).comp embedCore = embedCore.comp (ann i) := by
  refine core_ext fun b => ?_
  refine Subtype.ext ?_
  simp only [LinearMap.comp_apply, annOp]
  have hR : ((embedCore (ann i (coreState b)) : polyGaussCore (d := 3)) : L2d 3)
      = ((Real.sqrt ((b i : ℝ)) : ℝ) : ℂ) • hermiteMvLp (velIdx b - Finsupp.single i 1) := by
    rw [ann_coreState, map_smul, Submodule.coe_smul, embedCore_coe, coreState_coe,
      velUnitary_single, hermiteVel, velIdx_lower]
  rw [hR, embedCore_coreState, coreOp_coe, map_smul, pgLp_smul, annPoly_hermiteMvLp,
    velIdx_apply]

theorem intertwine_cre (i : Fin 3) : (creOp i).comp embedCore = embedCore.comp (cre i) := by
  refine core_ext fun b => ?_
  refine Subtype.ext ?_
  simp only [LinearMap.comp_apply, creOp]
  have hR : ((embedCore (cre i (coreState b)) : polyGaussCore (d := 3)) : L2d 3)
      = ((Real.sqrt ((b i : ℝ) + 1) : ℝ) : ℂ) • hermiteMvLp (velIdx b + Finsupp.single i 1) := by
    rw [cre_coreState, map_smul, Submodule.coe_smul, embedCore_coe, coreState_coe,
      velUnitary_single, hermiteVel, velIdx_raise]
  rw [hR, embedCore_coreState, coreOp_coe, map_smul, pgLp_smul, crePoly_hermiteMvLp,
    velIdx_apply]

theorem Intertwined.add {T S T' S'} (hT : Intertwined T T') (hS : Intertwined S S') :
    Intertwined (T + S) (T' + S') := fun x => by
  simp only [LinearMap.add_apply, hT x, hS x, map_add]

theorem Intertwined.sub {T S T' S'} (hT : Intertwined T T') (hS : Intertwined S S') :
    Intertwined (T - S) (T' - S') := fun x => by
  simp only [LinearMap.sub_apply, hT x, hS x, map_sub]

theorem Intertwined.smul {T T'} (c : ℂ) (hT : Intertwined T T') :
    Intertwined (c • T) (c • T') := fun x => by
  simp only [LinearMap.smul_apply, hT x, map_smul]

theorem Intertwined.comp {T S T' S'} (hT : Intertwined T T') (hS : Intertwined S S') :
    Intertwined (T.comp S) (T'.comp S') := fun x => by
  simp only [LinearMap.comp_apply, hS x, hT (S x)]

theorem Intertwined.id : Intertwined LinearMap.id LinearMap.id := fun _ => rfl

theorem Intertwined.sum {ι : Type*} (s : Finset ι)
    {T : ι → lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel}
    {T' : ι → (polyGaussCore (d := 3)) →ₗ[ℂ] (polyGaussCore (d := 3))}
    (h : ∀ i ∈ s, Intertwined (T i) (T' i)) :
    Intertwined (∑ i ∈ s, T i) (∑ i ∈ s, T' i) := fun x => by
  simp only [LinearMap.sum_apply]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i hi => h i hi x

theorem intertwined_ann (i : Fin 3) : Intertwined (ann i) (annOp i) := fun x =>
  congrFun (congrArg (fun F : lpFiniteModes Vel →ₗ[ℂ] (polyGaussCore (d := 3)) => ⇑F)
    (intertwine_ann i)) x

theorem intertwined_cre (i : Fin 3) : Intertwined (cre i) (creOp i) := fun x =>
  congrFun (congrArg (fun F : lpFiniteModes Vel →ₗ[ℂ] (polyGaussCore (d := 3)) => ⇑F)
    (intertwine_cre i)) x

theorem posOp_eq_ladder (i : Fin 3) : posOp i = annOp i + creOp i := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨p, rfl⟩ := (coreEquiv (d := 3)).surjective y
  simp only [posOp, annOp, creOp, coreOp_coreEquiv, LinearMap.add_apply, ← map_add]
  congr 1
  simp only [mulXPoly_apply, annPoly_apply, crePoly_apply]
  ring

theorem momOp_eq_ladder (i : Fin 3) :
    momOp i = (Complex.I / 2) • (creOp i - annOp i) := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨p, rfl⟩ := (coreEquiv (d := 3)).surjective y
  simp only [momOp, annOp, creOp, coreOp_coreEquiv, LinearMap.smul_apply, LinearMap.sub_apply,
    ← map_sub, ← map_smul]
  congr 1
  have hI : (C (Complex.I / 2) : MvPolynomial (Fin 3) ℂ) = C Complex.I * C (1 / 2 : ℂ) := by
    rw [← map_mul]
    congr 1
    ring
  have h2 : (C (1 / 2 : ℂ) : MvPolynomial (Fin 3) ℂ) * 2 = 1 := by
    rw [← map_ofNat C 2, ← map_mul]
    norm_num
  simp only [momPoly_apply, annPoly_apply, crePoly_apply, MvPolynomial.smul_eq_C_mul, map_neg,
    hI]
  linear_combination (C Complex.I * (pderiv i) p) * h2

theorem sqrtTwo_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  simp

theorem sqrtTwo_mul_self : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem intertwined_pos (i : Fin 3) :
    Intertwined (pos i) (((1 / Real.sqrt 2 : ℝ) : ℂ) • posOp i) := by
  rw [posOp_eq_ladder, add_comm (annOp i) (creOp i)]
  exact ((intertwined_cre i).add (intertwined_ann i)).smul _

theorem intertwined_mom (i : Fin 3) :
    Intertwined (mom i) (((Real.sqrt 2 : ℝ) : ℂ) • momOp i) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) • momOp i
      = (Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ)) • (creOp i - annOp i) := by
    rw [momOp_eq_ladder, smul_smul]
    congr 1
    have hne := sqrtTwo_ne_zero
    have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by rw [sq]; exact sqrtTwo_mul_self
    push_cast
    field_simp
    linear_combination hsq
  rw [hs]
  exact ((intertwined_cre i).sub (intertwined_ann i)).smul _

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
theorem intertwined_fieldV (i : Fin 3) :
    Intertwined (fieldV A c i)
      (((1 / Real.sqrt 2 : ℝ) : ℂ) • fieldOp A (fun j => Real.sqrt 2 * c j) i) := by
  have hsum : Intertwined (∑ k, ((A i k : ℝ) : ℂ) • pos k)
      (∑ k, ((A i k : ℝ) : ℂ) • (((1 / Real.sqrt 2 : ℝ) : ℂ) • posOp k)) :=
    Intertwined.sum _ fun k _ => (intertwined_pos k).smul _
  have hid : Intertwined (((c i : ℝ) : ℂ) • LinearMap.id)
      (((c i : ℝ) : ℂ) • LinearMap.id) := Intertwined.id.smul _
  have heq : ((1 / Real.sqrt 2 : ℝ) : ℂ) • fieldOp A (fun j => Real.sqrt 2 * c j) i
      = (∑ k, ((A i k : ℝ) : ℂ) • (((1 / Real.sqrt 2 : ℝ) : ℂ) • posOp k))
        + ((c i : ℝ) : ℂ) • LinearMap.id := by
    rw [fieldOp, smul_add, Finset.smul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    · rw [smul_smul]
      congr 1
      have hne := sqrtTwo_ne_zero
      push_cast
      field_simp
  rw [heq]
  exact hsum.add hid

theorem intertwined_canH :
    Intertwined (canH A c) (nsDiffH A (fun j => Real.sqrt 2 * c j)) := by
  have hscal : ((Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = 1 := by
    have hne := sqrtTwo_ne_zero
    push_cast
    field_simp
  have hterm : ∀ i : Fin 3,
      Intertwined (((1 : ℂ) / 2) • ((mom i).comp (fieldV A c i) + (fieldV A c i).comp (mom i)))
        (((1 : ℂ) / 2) • ((momOp i).comp (fieldOp A (fun j => Real.sqrt 2 * c j) i)
          + (fieldOp A (fun j => Real.sqrt 2 * c j) i).comp (momOp i))) := by
    intro i
    have hm := intertwined_mom i
    have hf := intertwined_fieldV A c i
    have h := ((hm.comp hf).add (hf.comp hm)).smul ((1 : ℂ) / 2)
    have heq : (((Real.sqrt 2 : ℝ) : ℂ) • momOp i).comp
          (((1 / Real.sqrt 2 : ℝ) : ℂ) • fieldOp A (fun j => Real.sqrt 2 * c j) i)
        + (((1 / Real.sqrt 2 : ℝ) : ℂ) • fieldOp A (fun j => Real.sqrt 2 * c j) i).comp
          (((Real.sqrt 2 : ℝ) : ℂ) • momOp i)
        = (momOp i).comp (fieldOp A (fun j => Real.sqrt 2 * c j) i)
          + (fieldOp A (fun j => Real.sqrt 2 * c j) i).comp (momOp i) := by
      rw [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_smul,
        smul_smul, smul_smul, hscal, mul_comm (((1 / Real.sqrt 2 : ℝ) : ℂ))
          (((Real.sqrt 2 : ℝ) : ℂ)), hscal, one_smul, one_smul]
    rw [← heq]
    exact h
  exact Intertwined.sum Finset.univ fun i _ => hterm i

end BookProof.NavierStokesFlow.DifferentialL2
namespace BookProof.NavierStokesFlow.DiffFarisLavine
theorem intertwined_nsDiffN (mu : ℝ) : Intertwined (velNcore mu) (nsDiffN mu) := by
  rw [nsDiffN_eq_ladder, velNcore]
  refine Intertwined.add ?_ (Intertwined.id.smul _)
  exact (Intertwined.sum Finset.univ fun i _ =>
    (intertwined_cre i).comp (intertwined_ann i)).smul _

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
theorem nsDiffH_embedCore (x : lpFiniteModes Vel) :
    ((nsDiffH A c (embedCore x) : polyGaussCore (d := 3)) : L2d 3)
      = velUnitary ((canH A (seqConst c) x : lpFiniteModes Vel) : L2I Vel) := by
  have hc : (fun j => Real.sqrt 2 * (seqConst c j)) = c := by
    funext j
    simp only [seqConst]
    field_simp
  have h := intertwined_canH A (seqConst c) x
  rw [hc] at h
  rw [h, embedCore_coe]

end BookProof.NavierStokesFlow.DiffFarisLavine

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.intertwined_nsDiffN
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.DiffFarisLavine













open MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.DifferentialL2


set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
theorem solution (mu : ℝ) : Intertwined (velNcore mu) (nsDiffN mu) := by
  exact BookProof.NavierStokesFlow.DiffFarisLavine.intertwined_nsDiffN mu
#print axioms solution
example : (∀ (mu : ℝ) ,  Intertwined (velNcore mu) (nsDiffN mu)) := @solution
