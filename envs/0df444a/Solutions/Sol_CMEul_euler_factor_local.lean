-- Prove2me | solution 1 for CMEul.euler_factor_local
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:24.9918+00:00
-- url     : https://prove2.me/submissions/9197e95d-c8d6-42ea-8e5a-f10fa2bf464e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_EulerFactorLocal
import Theorems.Thm_CMEul_two_le_absNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open CMEul
open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory
namespace CMEul
theorem _root_.solution : StepLocal := by
  intro F E _ _ _ _ _ _ M hM v hv hS
  classical
  have hN2 : (2 : ℝ) ≤ (Ideal.absNorm v : ℝ) := by exact_mod_cast two_le_absNorm v hv
  have hNpos : (0 : ℝ) < (Ideal.absNorm v : ℝ) := by linarith
  have hx1 : ((Ideal.absNorm v : ℕ) : ℝ) ^ (-(M : ℤ)) < 1 := by
    rw [zpow_neg, zpow_natCast]
    apply inv_lt_one_of_one_lt₀
    exact one_lt_pow₀ (by linarith) (by omega)
  rcases hS with ⟨P, hPm, hPv, hPc, hPN, hPu⟩ | ⟨P, Q, hPm, hQm, hPv, hQv, hPQ, hPc, hQc, hPN, hQN, hu⟩
  ·
    have heta : etaF F E v = -1 := by
      unfold etaF
      rw [if_pos ⟨P, ⟨hPm, hPv⟩, fun R hR => hPu R hR.1 hR.2⟩]
    let p0 : {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} :=
      ⟨P, hPm, hPv⟩
    have hval : eulerFac E M P = eulerF F E M v := by
      unfold eulerFac eulerF
      rw [if_pos hPc, heta, hPN]
      push_cast
      rw [Real.sqrt_sq hNpos.le]
    have := hasProd_single (f := fun c : {P : Ideal (𝓞 E) // P.IsMaximal ∧
        P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} => eulerFac E M c.1) p0 (fun b hb => by
      exfalso
      apply hb
      exact Subtype.ext (hPu b.1 b.2.1 b.2.2))
    simpa [p0, hval] using this
  ·
    have heta : etaF F E v = 1 := by
      unfold etaF
      rw [if_neg]
      rintro ⟨R, ⟨hRm, hRv⟩, hR⟩
      exact hPQ ((hR P ⟨hPm, hPv⟩).trans (hR Q ⟨hQm, hQv⟩).symm)
    let p0 : {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} :=
      ⟨P, hPm, hPv⟩
    let q0 : {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} :=
      ⟨Q, hQm, hQv⟩
    have hne : p0 ≠ q0 := fun h => hPQ (congrArg Subtype.val h)
    set y : ℝ := 1 - ((Ideal.absNorm v : ℕ) : ℝ) ^ (-(M : ℤ)) with hy
    have hypos : 0 < y := by rw [hy]; linarith
    have hP' : eulerFac E M P = y ^ (-(1 : ℝ) / 2) := by
      unfold eulerFac
      rw [if_neg (by rw [hPc]; exact fun h => hPQ h.symm), hPN]
    have hQ' : eulerFac E M Q = y ^ (-(1 : ℝ) / 2) := by
      unfold eulerFac
      rw [if_neg (by rw [hQc]; exact hPQ), hQN]
    have hval : eulerFac E M P * eulerFac E M Q = eulerF F E M v := by
      rw [hP', hQ', ← Real.rpow_add hypos]
      unfold eulerF
      rw [heta, one_pow, one_mul, ← hy]
      norm_num
      exact Real.rpow_neg_one y
    have := hasProd_prod_of_ne_finset_one (f := fun c : {P : Ideal (𝓞 E) // P.IsMaximal ∧
        P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} => eulerFac E M c.1) (s := {p0, q0})
      (L := SummationFilter.unconditional _) (fun b hb => by
      exfalso
      apply hb
      rcases hu b.1 b.2.1 b.2.2 with h | h
      · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext h))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h))))
    rw [Finset.prod_pair hne] at this
    simpa [p0, q0, hval] using this
end CMEul
