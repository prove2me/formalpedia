-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.twist_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:31.289866+00:00
-- url     : https://prove2.me/submissions/3f850efe-2c76-4ebf-bea1-488de857f46d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistB
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_main_twist_bound
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_twist_decomp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (m₀ s a₀ : ℕ) [NeZero (m₀ * s)] (hm : 0 < m₀) (h1 : 1 < s) (hodd : Odd s)
    (hsq : Squarefree s) (hcop : m₀.Coprime s) (ha : a₀.Coprime m₀) (X r k : ℝ)
    (e : Option (DirichletCharacter ℂ (m₀ * s) × ℝ)) (hX : 0 ≤ X) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2)
    (hli : 0 < liX X) (hk : |k| ≤ 1 / 2)
    (hb : ∀ b ∈ clsB m₀ s a₀, |(piAP X (m₀ * s) b : ℝ) - mainAP e b X| ≤ k * mainAP e b X)
    (hG : ∀ (χ : DirichletCharacter ℂ (m₀ * s)) (β : ℝ), e = some (χ, β) →
      (∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime s → χ (u : ZMod (m₀ * s)) = ((jacobiSym (u : ℤ) s : ℤ) : ℂ)) →
      |liX (X ^ β)| ≤ r * liX X) :
    |∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ)| ≤
      (4 * r + 2 * |k|) * (((PPset m₀ a₀ X).card : ℝ) + X ^ (1 / 2 : ℝ)) + X ^ (1 / 2 : ℝ) := by
  have hs : 0 < s := by omega
  obtain ⟨hd, hsumabs⟩ := twist_decomp m₀ s a₀ X hm hs hX (fun b => mainAP e b X) k hk hb
  beta_reduce at hd hsumabs
  have hmain := main_twist_bound m₀ s a₀ hm h1 hodd hsq hcop ha X r e hr0 hr hli hG
  have h2 : 2 * r * ∑ b ∈ clsB m₀ s a₀, |mainAP e b X| ≤
      2 * r * (2 * (((PPset m₀ a₀ X).card : ℝ) + X ^ (1 / 2 : ℝ))) :=
    mul_le_mul_of_nonneg_left hsumabs (by linarith)
  have h3 := abs_sub_abs_le_abs_sub (∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ))
    (∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * mainAP e b X)
  nlinarith [hd, hmain, h2, h3, abs_nonneg k]
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
