-- Prove2me | solution 1 for CuspidalType.theta_scalarUnit_eq_one_of_isCuspidalOfType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/2886cef2-8713-5d21-ac80-b606bd5be0b9

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_theta_scalarUnit_eq_one_of_isCuspidalOfType

set_option autoImplicit false

open Polynomial CuspidalType

namespace CuStSmallRows

variable {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {V' : Type*} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']

private noncomputable def sUnit (q : ℕ) [Fact q.Prime] (c : (ZMod q)ˣ) : (GaloisField q 2)ˣ :=
  Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c

private theorem torus_sUnit (c : (ZMod q)ˣ) : torus q (sUnit q c) = scalarElem q c := by
  apply Units.ext
  change LinearMap.toMatrix (quadBasis q) (quadBasis q)
      (Algebra.lmul (ZMod q) (GaloisField q 2) (algebraMap (ZMod q) (GaloisField q 2) (c : ZMod q))) =
    Matrix.scalar (Fin 2) (c : ZMod q)
  have hl : Algebra.lmul (ZMod q) (GaloisField q 2) (algebraMap (ZMod q) (GaloisField q 2) (c : ZMod q)) =
      (c : ZMod q) • LinearMap.id := by
    ext x
    simp [Algebra.smul_def]
  rw [hl, map_smul, LinearMap.toMatrix_id]
  ext i j
  simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]

private theorem scalarElem_smul' (c : (ZMod q)ˣ) (x : ProjLine q) : scalarElem q c • x = x := by
  induction x using Projectivization.ind with
  | h v hv =>
    change Matrix.GeneralLinearGroup.toLin (scalarElem q c) • Projectivization.mk (ZMod q) v hv = _
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨(c : ZMod q), ?_⟩
    change (c : ZMod q) • v = Matrix.toLin' (Matrix.scalar (Fin 2) (c : ZMod q)) v
    rw [Matrix.toLin'_apply]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]

private theorem ind_scalarElem' (c : (ZMod q)ˣ) : ind q K (scalarElem q c) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro x r
  rw [ind, Representation.ofMulActionFinsupp_single, scalarElem_smul']
  rfl

end CuStSmallRows

open CuStSmallRows in

theorem solution {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {θ : (GaloisField q 2)ˣ →* Kˣ} {ρ : Representation K (GL2 q) V}
    (h : IsCuspidalOfType θ ρ) (c : (ZMod q)ˣ) :
    θ (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c) = 1 := by
  change θ (sUnit q c) = 1
  have hfield := h.torus_charpoly (sUnit q c)
  rw [torus_sUnit, h.central, ind_scalarElem', ← Module.End.one_eq_id, ← Module.End.one_eq_id,
    LinearMap.charpoly_one, LinearMap.charpoly_one, h.finrank_eq, finrank_ind] at hfield
  have hq : q + 1 = (q - 1) + 2 := by
    have := (Fact.out : q.Prime).one_lt
    omega
  rw [hq, pow_add] at hfield
  have hquad := mul_left_cancel₀ (pow_ne_zero (q - 1) (X_sub_C_ne_zero (1 : K))) (by simpa using hfield)
  have hev := congrArg (Polynomial.eval (1 : K)) hquad
  simp only [eval_mul, eval_sub, eval_X, eval_C, eval_pow, eval_one, sub_self] at hev
  have hor : (1 : K) - ((θ (sUnit q c) : Kˣ) : K) = 0 ∨ (1 : K) - (((θ (sUnit q c) : Kˣ) : K))⁻¹ = 0 := by
    simpa using hev
  have hval : ((θ (sUnit q c) : Kˣ) : K) = 1 := by
    rcases hor with h1 | h1
    · exact (sub_eq_zero.1 h1).symm
    · exact inv_eq_one.1 (sub_eq_zero.1 h1).symm
  exact Units.ext (by rw [Units.val_one]; exact hval)

end S_CuspidalType_theta_scalarUnit_eq_one_of_isCuspidalOfType
end P2MW
export P2MW.S_CuspidalType_theta_scalarUnit_eq_one_of_isCuspidalOfType (solution)
