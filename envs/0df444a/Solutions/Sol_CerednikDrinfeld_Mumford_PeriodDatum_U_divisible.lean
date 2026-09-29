-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.PeriodDatum.U_divisible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/4f6ed23c-e13d-58d6-9d2d-69b96101119a

import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Mathlib.LinearAlgebra.FreeModule.PID
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_PeriodDatum_U_divisible

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem solution
    {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}
    (P : PeriodDatum D K L ord) (hroots : ∀ (x : Lˣ) (n : ℕ), 0 < n → ∃ y : Lˣ, y ^ n = x) :
    ∀ u : ↥P.U, ∀ n : ℕ, 0 < n → ∃ u' : ↥P.U, n • u' = u := by
  intro u n hn

  obtain ⟨m, ⟨b⟩⟩ := Submodule.nonempty_basis_of_pid (Pi.basisFun ℤ E) (ribbonKernel D)

  have hex : ∀ i : Fin m, ∃ y : Additive Lˣ, n • y = (u : P.TorusPoints) (b i) := by
    intro i
    obtain ⟨y, hy⟩ := hroots (Additive.toMul ((u : P.TorusPoints) (b i))) n hn
    exact ⟨Additive.ofMul y, by rw [← ofMul_pow, hy, ofMul_toMul]⟩
  choose r hr using hex
  let ψ : P.TorusPoints := b.constr ℤ r
  have hψ : n • ψ = (u : P.TorusPoints) := by
    refine b.ext fun i => ?_
    rw [LinearMap.smul_apply, b.constr_basis ℤ r i, hr]
  have hψU : ψ ∈ P.U := by
    have hu := u.2
    simp only [PeriodDatum.U, Submodule.mem_comap] at hu ⊢
    obtain ⟨⟨a, ha⟩, hau⟩ := (Submodule.mem_torsion_iff _).mp hu
    have hau' : a • P.periodLattice.mkQ (u : P.TorusPoints) = 0 := hau
    refine (Submodule.mem_torsion_iff _).mpr
      ⟨⟨a * (n : ℤ), mem_nonZeroDivisors_of_ne_zero
        (mul_ne_zero (nonZeroDivisors.ne_zero ha) (by exact_mod_cast hn.ne'))⟩, ?_⟩
    show (a * (n : ℤ)) • P.periodLattice.mkQ ψ = 0
    rw [mul_smul, natCast_zsmul, ← map_nsmul, hψ, hau']
  refine ⟨⟨ψ, hψU⟩, ?_⟩
  apply Subtype.ext
  exact hψ

end S_CerednikDrinfeld_Mumford_PeriodDatum_U_divisible
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_PeriodDatum_U_divisible (solution)
