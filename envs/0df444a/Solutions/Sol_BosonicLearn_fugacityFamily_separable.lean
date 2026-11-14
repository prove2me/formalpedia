-- Prove2me | solution 1 for BosonicLearn.fugacityFamily_separable
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T09:46:01.327564+00:00
-- url     : https://prove2.me/submissions/5885ab9b-a42d-4ed6-a60d-ee6436cf5a4f

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_BosonicLearn_fugacityFamily
import Definitions.Def_BosonicLearn_Gsupp
import Theorems.Thm_BosonicLearn_density_tendsto_of_entrywise
import Theorems.Thm_BosonicLearn_fugacityFamily_promiseClass

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize NuclearExpansion IsDensity)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open Filter Topology
open scoped ENNReal

open BosonicLearn

noncomputable section

/-! ### Symmetry of the trace norm -/

private lemma traceSize_neg_le {I : Type} (X : Matrix I I ℂ) : traceSize (-X) ≤ traceSize X := by
  refine le_iInf fun e => ?_
  let e' : NuclearExpansion (-X) :=
    { left := fun k => -e.left k
      right := e.right
      summable := by simpa using e.summable
      coefficients := by
        intro i j
        simp [e.coefficients i j, tsum_neg] }
  refine (iInf_le _ e').trans (le_of_eq ?_)
  simp [e']

private lemma traceSize_sub_comm {I : Type} (A B : Matrix I I ℂ) :
    traceSize (A - B) = traceSize (B - A) := by
  refine le_antisymm ?_ ?_
  · rw [← neg_sub B A]
    exact traceSize_neg_le _
  · rw [← neg_sub A B]
    exact traceSize_neg_le _

/-! ### Continuity of the Fock coefficients of the family -/

private lemma continuous_family (n : ℕ) (ν ξ : ℝ) :
    Continuous fun X : Herm0 n => fugacityFamily ν ξ X := by
  have h1 : Continuous fun X : Herm0 n => (X : Matrix (Fin n) (Fin n) ℂ) := continuous_subtype_val
  have h2 : Continuous fun X : Herm0 n => (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ) :=
    h1.const_smul (ξ : ℂ)
  have h3 : Continuous fun X : Herm0 n =>
      (1 : Matrix (Fin n) (Fin n) ℂ) + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ) :=
    continuous_const.add h2
  have h4 : Continuous fun X : Herm0 n => ((ν / ((1 - 4 * ξ) * (1 + ν)) : ℝ) : ℂ) •
      ((1 : Matrix (Fin n) (Fin n) ℂ) + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)) :=
    h3.const_smul (((ν / ((1 - 4 * ξ) * (1 + ν)) : ℝ) : ℂ))
  exact h4

/-- Each Fock coefficient of `ρ_{R_X}` is a continuous function of `X`: a determinant times a finite sum of
monomials in the entries of `R_X`. -/
private lemma continuous_entry (n : ℕ) (ν ξ : ℝ) (u v : Occupation (Fin n)) :
    Continuous fun X : Herm0 n => fugacityCoeff (fugacityFamily ν ξ X) u v := by
  have hR := continuous_family n ν ξ
  have hdet : Continuous fun X : Herm0 n => (1 - fugacityFamily ν ξ X).det :=
    (continuous_const.sub hR).matrix_det
  have hg : Continuous fun X : Herm0 n => gammaFock (fugacityFamily ν ξ X) u v := by
    unfold gammaFock
    exact continuous_const.mul (continuous_finsetSum _ fun M _ => continuous_finsetProd _ fun i _ =>
      continuous_finsetProd _ fun j _ => ((hR.matrix_elem i j).pow _).div_const _)
  exact hdet.mul hg

/-! ### `G_supp` is a nonempty separable space -/

private lemma zero_mem_gsupp (n : ℕ) : (0 : Herm0 n) ∈ Gsupp n := by
  simp [Gsupp, WHMultiplicativity.schattenNorm]

private instance (n : ℕ) : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))

private instance (n : ℕ) : SecondCountableTopology (Herm0 n) :=
  TopologicalSpace.Subtype.secondCountableTopology (Herm0 n : Set (Matrix (Fin n) (Fin n) ℂ))

theorem solution (n : ℕ) (ν ξ : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hξ0 : 0 < ξ)
    (hξ1 : ξ < 1 / 32) :
    ∃ D : ℕ → Herm0 n, (∀ k, D k ∈ Gsupp n) ∧ ∀ X ∈ Gsupp n, ∀ η : ℝ, 0 < η →
      ∃ k, traceSize (fugacityCoeff (fugacityFamily ν ξ X) -
        fugacityCoeff (fugacityFamily ν ξ (D k))) < ENNReal.ofReal η := by
  have hdens : ∀ X ∈ Gsupp n, IsDensity (fugacityCoeff (fugacityFamily ν ξ X)) := by
    intro X hX
    obtain ⟨ρ, hρ, -⟩ := fugacityFamily_promiseClass n ν ξ hν0 hν1 hξ0 hξ1 X hX
    rw [← hρ]
    exact ρ.density
  have : Nonempty ↥(Gsupp n) := ⟨⟨0, zero_mem_gsupp n⟩⟩
  refine ⟨fun k => (TopologicalSpace.denseSeq ↥(Gsupp n) k : Herm0 n), fun k =>
    (TopologicalSpace.denseSeq ↥(Gsupp n) k).2, fun X hX η hη => ?_⟩
  have hx : (⟨X, hX⟩ : ↥(Gsupp n)) ∈ closure (Set.range (TopologicalSpace.denseSeq ↥(Gsupp n))) :=
    TopologicalSpace.denseRange_denseSeq ↥(Gsupp n) ⟨X, hX⟩
  obtain ⟨y, hy, hyx⟩ := mem_closure_iff_seq_limit.mp hx
  have hent : ∀ u v : Occupation (Fin n),
      Tendsto (fun m => fugacityCoeff (fugacityFamily ν ξ (y m : Herm0 n)) u v) atTop
        (𝓝 (fugacityCoeff (fugacityFamily ν ξ X) u v)) := by
    intro u v
    have hc : Continuous fun z : ↥(Gsupp n) => fugacityCoeff (fugacityFamily ν ξ (z : Herm0 n)) u v :=
      (continuous_entry n ν ξ u v).comp continuous_subtype_val
    exact (hc.tendsto ⟨X, hX⟩).comp hyx
  have ht := density_tendsto_of_entrywise
    (fun m => fugacityCoeff (fugacityFamily ν ξ (y m : Herm0 n)))
    (fugacityCoeff (fugacityFamily ν ξ X)) (fun m => hdens _ (y m).2) (hdens X hX) hent
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal η := ENNReal.ofReal_pos.mpr hη
  obtain ⟨m, hm⟩ := ((tendsto_order.1 ht).2 _ hpos).exists
  obtain ⟨k, hk⟩ := hy m
  refine ⟨k, ?_⟩
  rw [traceSize_sub_comm]
  show traceSize (fugacityCoeff (fugacityFamily ν ξ (TopologicalSpace.denseSeq ↥(Gsupp n) k : Herm0 n)) -
    fugacityCoeff (fugacityFamily ν ξ X)) < ENNReal.ofReal η
  rw [hk]
  exact hm
