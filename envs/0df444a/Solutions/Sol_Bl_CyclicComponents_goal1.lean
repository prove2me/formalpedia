-- Prove2me | solution 1 for Bl.CyclicComponents.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:53.453846+00:00
-- url     : https://prove2.me/submissions/cc7ee9d6-3a68-4ce2-9911-a07468b6dad0

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_PropositionOneCentralCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleProbSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaLWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartEqIff
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartSpec
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSquarefreeCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRTypeCountExact
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleTypeProb
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8


section
namespace Bl.CyclicComponents
private lemma cyc {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (hirr : ∀ U : Submodule ℂ V, (∀ g : G, ∀ x ∈ U, ρ g x ∈ U) → U = ⊥ ∨ U = ⊤)
    (w : V) (hw : w ≠ 0) (S : Submodule ℂ V) (f : Module.End ℂ V)
    (hf : ∀ g : G, f (ρ g w) ∈ S) : ∀ v, f v ∈ S := by
  intro v
  have hU : Submodule.span ℂ (Set.range fun g => ρ g w) = ⊤ := by
    have hinv : ∀ g : G, ∀ x ∈ Submodule.span ℂ (Set.range fun g => ρ g w),
        ρ g x ∈ Submodule.span ℂ (Set.range fun g => ρ g w) := by
      intro g x hx
      have hle : Submodule.span ℂ (Set.range fun g => ρ g w) ≤
          (Submodule.span ℂ (Set.range fun g => ρ g w)).comap (ρ g) := by
        rw [Submodule.span_le]
        rintro _ ⟨g', rfl⟩
        exact Submodule.subset_span ⟨g * g', by simp [map_mul]⟩
      exact hle hx
    rcases hirr _ hinv with h | h
    · exfalso
      apply hw
      have hmem : w ∈ Submodule.span ℂ (Set.range fun g => ρ g w) :=
        Submodule.subset_span ⟨1, by simp⟩
      rw [h] at hmem
      simpa using hmem
    · exact h
  have hle : Submodule.span ℂ (Set.range fun g => ρ g w) ≤ S.comap f := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hf g
  rw [hU] at hle
  exact hle Submodule.mem_top
private lemma core {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (W : Submodule ℂ V) (P : Module.End ℂ V)
    (hPW : ∀ v, P v ∈ W) (hPfix : ∀ w ∈ W, P w = w)
    (hcomm : ∀ g g' : G, P * ρ g * P * (P * ρ g' * P) = P * ρ g' * P * (P * ρ g * P))
    (hirr : ∀ U : Submodule ℂ V, (∀ g : G, ∀ x ∈ U, ρ g x ∈ U) → U = ⊥ ∨ U = ⊤) :
    Module.finrank ℂ W ≤ 1 := by
  by_cases hW : W = ⊥
  · rw [hW]
    simp
  have hB : ∀ g : G, ∀ w ∈ W, P (ρ g w) = (P * ρ g * P) w := by
    intro g w hw
    simp [hPfix w hw]
  have hscal : ∀ h : G, ∃ μ : ℂ, ∀ x ∈ W, (P * ρ h * P) x = μ • x := by
    intro h
    have hBW : ∀ x ∈ W, (P * ρ h * P) x ∈ W := fun x _ => by
      simp only [Module.End.mul_apply]
      exact hPW _
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((P * ρ h * P).restrict hBW)
    obtain ⟨w, hwv⟩ := hμ.exists_hasEigenvector
    have hw1 := hwv.apply_eq_smul
    have hw2 : (P * ρ h * P) (w : V) = μ • (w : V) := by
      have := congrArg Subtype.val hw1
      simpa [LinearMap.restrict_apply] using this
    have hw0 : (w : V) ≠ 0 := by
      intro h0
      apply hwv.2
      exact Subtype.ext h0
    have key := cyc ρ hirr (w : V) hw0 ((P * ρ h * P).eigenspace μ) P (by
      intro g
      rw [Module.End.mem_eigenspace_iff, hB g w w.2]
      rw [← Module.End.mul_apply, hcomm h g, Module.End.mul_apply, hw2, map_smul])
    refine ⟨μ, fun x hx => ?_⟩
    have := Module.End.mem_eigenspace_iff.mp (key x)
    rwa [hPfix x hx] at this
  obtain ⟨w0, hw0W, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have key := cyc ρ hirr w0 hw0 (ℂ ∙ w0) P (by
    intro g
    obtain ⟨μ, hμ⟩ := hscal g
    rw [hB g w0 hw0W, hμ w0 hw0W]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hle : W ≤ ℂ ∙ w0 := by
    intro x hx
    rw [← hPfix x hx]
    exact key x
  calc Module.finrank ℂ W ≤ Module.finrank ℂ (ℂ ∙ w0) := Submodule.finrank_mono hle
    _ = 1 := finrank_span_singleton hw0
end Bl.CyclicComponents
end

set_option autoImplicit false
open Bl Bl.CyclicComponents
namespace Bl.CyclicComponents
theorem _root_.solution :
  ∀ {G : Type} [inst : Group.{0} G] [inst_1 : Fintype.{0} G] {V : Type} [inst_2 : AddCommGroup.{0} V]
  [inst_3 : Module.{0, 0} Complex V] [FiniteDimensional.{0, 0} Complex V] (ρ : Representation.{0, 0, 0} Complex G V)
  (J : Subgroup.{0} G) (χ : MonoidHom.{0, 0} (Subtype.{1} fun (x : G) ↦ Membership.mem.{0, 0} J x) (Units.{0} Complex)),
  (∀ (g g' : G),
      Eq.{1}
        (HMul.hMul.{0, 0, 0}
          (HMul.hMul.{0, 0, 0}
            (HMul.hMul.{0, 0, 0} (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ)
              (DFunLike.coe.{1, 1, 1} (MonoidAlgebra.of.{0, 0} Complex G) g))
            (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ))
          (HMul.hMul.{0, 0, 0}
            (HMul.hMul.{0, 0, 0} (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ)
              (DFunLike.coe.{1, 1, 1} (MonoidAlgebra.of.{0, 0} Complex G) g'))
            (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ)))
        (HMul.hMul.{0, 0, 0}
          (HMul.hMul.{0, 0, 0}
            (HMul.hMul.{0, 0, 0} (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ)
              (DFunLike.coe.{1, 1, 1} (MonoidAlgebra.of.{0, 0} Complex G) g'))
            (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ))
          (HMul.hMul.{0, 0, 0}
            (HMul.hMul.{0, 0, 0} (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ)
              (DFunLike.coe.{1, 1, 1} (MonoidAlgebra.of.{0, 0} Complex G) g))
            (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ)))) →
    Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.IsIrr ρ →
      LE.le.{0}
        (Module.finrank.{0, 0} Complex
          (Subtype.{1} fun (x : V) ↦
            Membership.mem.{0, 0}
              (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.eqvSpace ρ
                (fun (u : Subtype.{1} fun (x : G) ↦ Membership.mem.{0, 0} J x) ↦ Subtype.val.{1} u)
                fun (u : Subtype.{1} fun (x : G) ↦ Membership.mem.{0, 0} J x) ↦
                Units.val.{0} (DFunLike.coe.{1, 1, 1} χ u))
              x))
        1 := by
  intro G inst inst_1 V inst_2 inst_3 inst_4 ρ J χ hcomm hirr
  classical
  have hirr2 := hirr
  rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.IsIrr.eq_def] at hirr2
  obtain ⟨P, hPdef⟩ : ∃ P : Module.End ℂ V, P = ρ.asAlgebraHom (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ) :=
    ⟨_, rfl⟩
  have hP : ∀ v, P v = ∑ u : J, ((↑(Nat.card J) : ℂ)⁻¹ * ↑(χ u)⁻¹) • ρ ↑u v := by
    intro v
    rw [hPdef, Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem.eq_def, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [map_smul, LinearMap.smul_apply, Representation.asAlgebraHom_of]
  have hPW : ∀ v, P v ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.eqvSpace ρ (fun u : J => u.val) (fun u => (χ u).val) := by
    intro v
    rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.eqvSpace.eq_def]
    show ∀ u : J, ρ ↑u (P v) = (χ u : ℂ) • P v
    intro u0
    rw [hP, map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft u0) _ _ (fun u => ?_)
    simp only [Equiv.coe_mulLeft, map_smul, Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul,
      mul_inv_rev, Units.val_mul]
    congr 1
    linear_combination (-((↑(Nat.card J) : ℂ)⁻¹ * ↑(χ u)⁻¹)) * Units.inv_mul (χ u0)
  have hPfix : ∀ w ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.eqvSpace ρ (fun u : J => u.val) (fun u => (χ u).val), P w = w := by
    intro w hw
    rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.eqvSpace.eq_def] at hw
    have hw' : ∀ u : J, ρ ↑u w = (χ u : ℂ) • w := hw
    rw [hP]
    simp only [hw', smul_smul, mul_assoc, Units.inv_mul, mul_one]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, mul_inv_cancel₀, one_smul]
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcomm2 : ∀ g g' : G, P * ρ g * P * (P * ρ g' * P) = P * ρ g' * P * (P * ρ g * P) := by
    intro g g'
    have := congrArg ρ.asAlgebraHom (hcomm g g')
    simpa [map_mul, Representation.asAlgebraHom_of, hPdef] using this
  exact core ρ _ P hPW hPfix hcomm2 hirr2.2
end Bl.CyclicComponents
