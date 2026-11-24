-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.normRepCount_inert_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:37.613967+00:00
-- url     : https://prove2.me/submissions/f215e62d-aa94-4fbc-8dc6-8fc088b97cef

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountSplitOne
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormResidues_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormResidues_natCard_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormResidues_sigEquiv_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_card_herm_norm_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_sub_conjO_notMem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open NormResidues
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (M : ℕ) (hM : 1 ≤ M) (n : 𝓞 K) (hn : conjO K n = n)
    (hnP : n ∉ P) (q : ℕ) (hq : Ideal.absNorm P = q ^ 2) :
    (normRepCount K P M n : ℤ) = (q : ℤ) ^ (M - 1) * ((q : ℤ) ^ M - (-1) ^ M) := by
  have := hP
  have := finite_quot hP
  let _ : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hq' : Fintype.card (𝓞 K ⧸ P) = q ^ 2 := by
    rw [Fintype.card_eq_nat_card, natCard_quot, hq]
  have hne : ∃ x, sigEquiv P hc x ≠ x := by
    obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
    refine ⟨Ideal.Quotient.mk P θ, fun h => hθ ?_⟩
    rw [sigEquiv_mk] at h
    exact Ideal.Quotient.eq.mp h.symm
  have hcσ : sigEquiv P hc (Ideal.Quotient.mk P n) = Ideal.Quotient.mk P n := by
    rw [sigEquiv_mk, hn]
  have hc0 : Ideal.Quotient.mk P n ≠ 0 := fun h => hnP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have key : ∀ x : Fin M → 𝓞 K ⧸ P,
      (∃ y : Fin M → 𝓞 K, (∀ i, Ideal.Quotient.mk P (y i) = x i) ∧
        Ideal.Quotient.mk P (∑ i, conjO K (y i) * y i) = Ideal.Quotient.mk P n) ↔
      ∑ i, sigEquiv P hc (x i) * x i = Ideal.Quotient.mk P n := by
    intro x
    constructor
    · rintro ⟨y, hy, h⟩
      rw [← h, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← hy i, sigEquiv_mk]
    · intro h
      choose y hy using fun i => Ideal.Quotient.mk_surjective (x i)
      refine ⟨y, hy, ?_⟩
      rw [← h, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← hy i, sigEquiv_mk]
  unfold normRepCount
  rw [Nat.card_congr (Equiv.subtypeEquivRight key)]
  exact card_herm_norm_eq (sigEquiv P hc) (fun x => sigHom_sigHom P hc x) hne q hq' M hM _ hcσ hc0
end Formalism.HermitianLattices.Ext.L3
