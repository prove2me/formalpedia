-- Prove2me | solution 1 for Formalism.HC.Landau.zero_free_of_Chebyshev_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:15:33.210638+00:00
-- url     : https://prove2.me/submissions/8ed46dbd-391d-407e-b8f7-63f2091780d6

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Landau
import Theorems.Thm_Formalism_HC_Landau_re_gChi
import Theorems.Thm_Formalism_HC_Landau_landau_family
import Theorems.Thm_Formalism_HC_Landau_inv_eq_of_isReal
import Theorems.Thm_Formalism_HC_Landau_eq_one_of_chi
import Theorems.Thm_Formalism_HC_Landau_one_inv
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_PChar_inv_inv
import Theorems.Thm_Formalism_landauIteratedDerivatives_key
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism Formalism.HC Formalism.HC.Landau
open Formalism ArithmeticFunction
namespace Formalism.HC.Landau
theorem _root_.solution (Lv : Level) : Lv.ChebyshevGrowthImpliesZeroFree := by
  classical
  intro θ h0 h1 y0 hG ψ hψ s hs
  have hmem : ∀ ξ, ξ ∈ Lv.Nt ↔ ξ ≠ PChar.one ∧ ξ ∈ Lv.KEPT := fun ξ => by
    unfold Level.Nt
    rw [Finset.mem_erase]
  set k : PChar → ℕ := fun ξ => if Lv.psK = some ξ then 3 * Lv.o + 1 else 1 with hk
  have hps : ∀ ξ, Lv.psK = some ξ → Lv.psK = some ξ.inv := fun ξ h => by
    rw [inv_eq_of_isReal (Lv.psK_spec ξ h).2.2]; exact h
  have hki : ∀ ξ, k ξ.inv = k ξ := fun ξ => by
    have : Lv.psK = some ξ.inv ↔ Lv.psK = some ξ := ⟨fun h => by simpa only [PChar.inv_inv] using hps _ h, hps ξ⟩
    simp only [hk, this]
  have hk0 : ∀ ξ, 0 < k ξ := fun ξ => by
    simp only [hk]
    split_ifs <;> omega
  have hp : (0 : ℝ) < 3 * (Lv.o : ℝ) + 1 := by positivity
  have hkw : ∀ ξ, (k ξ : ℝ) = (3 * (Lv.o : ℝ) + 1) * Lv.wt ξ := fun ξ => by
    simp only [hk, Level.wt]
    split_ifs
    · push_cast; ring
    · rw [mul_inv_cancel₀ hp.ne', Nat.cast_one]
  have hne : ∀ ξ ∈ Lv.Nt, ξ.χ ≠ 1 := fun ξ h e => ((hmem ξ).1 h).1 (eq_one_of_chi e)
  have key := landau_family (ι := Σ _ : PChar, ℕ) (fun i => i.1) (fun i => ⟨i.1.inv, i.2⟩)
    (fun i => by obtain ⟨a, b⟩ := i; simp only [PChar.inv_inv]) (fun _ => rfl)
    (Lv.Nt.sigma fun ξ => Finset.range (k ξ)) (fun i h => hne _ (Finset.mem_sigma.1 h).1)
    (fun i h => by
      obtain ⟨a1, a2⟩ := Finset.mem_sigma.1 h
      obtain ⟨b1, b2⟩ := (hmem _).1 a1
      refine Finset.mem_sigma.2 ⟨(hmem _).2 ⟨fun e => b1 ?_, Lv.inv_mem _ b2⟩, ?_⟩
      · have e' : i.1.inv = PChar.one := e
        rw [← i.1.inv_inv, e', one_inv]
      · show i.2 ∈ Finset.range (k i.1.inv)
        rw [hki]; exact a2)
    (3 * Lv.o + 1) (by omega) θ h0 h1 (3 * Lv.o + 1) y0 (fun y hy => by
      have e := hG y hy
      unfold Level.Gm at e
      have e3 := mul_le_mul_of_nonneg_left e hp.le
      rw [mul_add, Finset.mul_sum] at e3
      rw [Finset.sum_sigma]
      push_cast
      refine le_of_eq_of_le ?_ e3
      congr 1
      refine Finset.sum_congr rfl fun ξ h => ?_
      show ∑ _j ∈ Finset.range (k ξ), Gchi ξ.χ y = _
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hkw, re_gChi ξ.χ (hne ξ h) y, mul_assoc]) s hs
  by_cases e : ψ = PChar.one
  · subst e
    have : DirichletCharacter.LFunction PChar.one.χ = riemannZeta := DirichletCharacter.LFunction_modOne_eq (χ := (1 : DirichletCharacter ℂ 1))
    rw [this]
    exact key.1
  · exact key.2 ⟨ψ, 0⟩ (Finset.mem_sigma.2 ⟨(hmem ψ).2 ⟨e, hψ⟩, Finset.mem_range.2 (hk0 ψ)⟩)
end Formalism.HC.Landau
