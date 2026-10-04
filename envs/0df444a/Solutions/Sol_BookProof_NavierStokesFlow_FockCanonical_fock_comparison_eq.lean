-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockCanonical.fock_comparison_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T13:10:25.480857+00:00
-- url     : https://prove2.me/submissions/96a62ebf-c4b7-4876-af47-1803cf98915f

import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Definitions.Def_ChapterBosonicCCR
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa

set_option autoImplicit false

open BookProof.Bosonic
open BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical

open scoped ENNReal

open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

theorem f5d9_alg (I S A B C D E F X1 X2 X3 X4 Xa k a : ℂ) (hI : I ^ 2 = -1)
    (hS : S * S = k / 2) (h1 : D * E = a + 1) (h2 : A * C * X2 = a * Xa) (h3 : X3 = Xa) :
    I * S * (A * (I * S * (B * X1 - C * X2)) - D * (I * S * (E * X3 - F * X4)))
      + S * (A * (S * (B * X1 + C * X2)) + D * (S * (E * X3 + F * X4)))
      = k * (2 * a + 1) * Xa := by
  subst h3
  linear_combination (S * S * (A * B * X1 - A * C * X2 - D * E * X3 + D * F * X4)) * hI
    + 2 * S * S * h2 + 2 * S * S * X3 * h1 + 2 * (2 * a + 1) * X3 * hS

theorem f5d9_dn_up {d : ℕ} (i : Fin d) (α : Occ d) : dn i (up i α) = α := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [up, dn]
  · simp [up, dn, hj]

theorem f5d9_ann_apply {d : ℕ} (i : Fin d) (x : lpFiniteModes (Occ d)) (α : Occ d) :
    (((ann i x : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α
      = (Real.sqrt ((α i : ℝ) + 1) : ℂ) * (((x : L2I (Occ d)) : Occ d → ℂ) (up i α)) := rfl

theorem f5d9_cre_apply {d : ℕ} (i : Fin d) (x : lpFiniteModes (Occ d)) (α : Occ d) :
    (((cre i x : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α
      = (Real.sqrt (α i : ℝ) : ℂ) * (((x : L2I (Occ d)) : Occ d → ℂ) (dn i α)) := rfl

theorem f5d9_mom_apply {d : ℕ} (κ : Fin d → ℝ) (i : Fin d) (x : lpFiniteModes (Occ d))
    (α : Occ d) :
    (((mom κ i x : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α
      = Complex.I * (Real.sqrt (κ i / 2) : ℂ) *
        ((((cre i x : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α
          - (((ann i x : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α) := by
  simp only [FockCanonical.mom, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul,
    Submodule.coe_sub, lp.coeFn_smul, lp.coeFn_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]

theorem f5d9_drift_apply {d : ℕ} (κ : Fin d → ℝ) (i : Fin d) (x : lpFiniteModes (Occ d))
    (α : Occ d) :
    (((drift κ i x : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α
      = (Real.sqrt (κ i / 2) : ℂ) *
        ((((cre i x : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α
          + (((ann i x : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α) := by
  simp only [FockCanonical.drift, LinearMap.smul_apply, LinearMap.add_apply, Submodule.coe_smul,
    Submodule.coe_add, lp.coeFn_smul, lp.coeFn_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul]

theorem f5d9_mode {d : ℕ} {κ : Fin d → ℝ} (i : Fin d) (hκ : 0 ≤ κ i)
    (x : lpFiniteModes (Occ d)) (α : Occ d) :
    (((((mom κ i).comp (mom κ i) + (drift κ i).comp (drift κ i)) x : lpFiniteModes (Occ d))
        : L2I (Occ d)) : Occ d → ℂ) α
      = (κ i : ℂ) * (2 * (α i : ℂ) + 1) * (((x : L2I (Occ d)) : Occ d → ℂ) α) := by
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.coe_add,
    lp.coeFn_add, Pi.add_apply]
  simp only [f5d9_mom_apply, f5d9_drift_apply, f5d9_cre_apply, f5d9_ann_apply]
  refine f5d9_alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Complex.I_sq ?_ ?_ ?_ ?_
  · rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
    push_cast
    ring
  · have hup : (up i α) i = α i + 1 := by simp [up]
    rw [hup]
    push_cast
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  · by_cases h0 : α i = 0
    · simp [h0]
    · have h1 : 1 ≤ α i := by omega
      have hdn : (dn i α) i = α i - 1 := by simp [dn]
      rw [up_dn i h1, hdn, ← Complex.ofReal_mul]
      have hc : (((α i - 1 : ℕ) : ℝ) + 1) = (α i : ℝ) := by
        rw [Nat.cast_sub h1]
        push_cast
        ring
      rw [hc, Real.mul_self_sqrt (by positivity)]
      push_cast
      ring
  · rw [f5d9_dn_up]

open BookProof.Bosonic BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockCanonical BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.FockManyMode BookProof.NavierStokesFlow.HermiteCanonical in
theorem solution {d : ℕ} {κ : Fin d → ℝ} (hκ : ∀ i, 0 ≤ κ i) :
    (lpFiniteModes (Occ d)).subtype.comp
        ((∑ i, ((mom κ i).comp (mom κ i) + (drift κ i).comp (drift κ i))) + LinearMap.id)
      = (diagMax (fockSym κ)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (fockSym κ))) := by
  refine LinearMap.ext fun x => ?_
  refine lp.ext (funext fun α => ?_)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, diagMax_coe, Submodule.coe_inclusion,
    Submodule.subtype_apply, LinearMap.add_apply, LinearMap.id_apply, Submodule.coe_add,
    lp.coeFn_add, Pi.add_apply, LinearMap.sum_apply, Submodule.coe_sum,
    lp.coeFn_sum, Finset.sum_apply]
  simp only [f5d9_mode _ (hκ _)]
  simp only [fockSym]
  push_cast
  rw [add_mul, Finset.sum_mul, one_mul]
