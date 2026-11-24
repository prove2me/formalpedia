-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.index_ideal_smul_le_norm_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:36.422446+00:00
-- url     : https://prove2.me/submissions/a1627b0c-749a-4e1f-8094-09b2a6be19a5

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_index_ideal_smul_top_le_norm_pow
import Theorems.Thm_Formalism_SLP_P_CountO_LIB_submodule
import Theorems.Thm_Formalism_SLP_P_CountO_TF_submodule
import Theorems.Thm_Formalism_SLP_P_CountO_index_comap_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.SLP.P.CountO NumberField
open scoped nonZeroDivisors
open NumberField Formalism.SLP.P.CountO
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {E : Type} [Field E] [NumberField E] (k : ℕ) : ∀ (N : ℕ) (I : Ideal (𝓞 E)), I ≠ ⊥ →
    Ideal.absNorm I = N → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X],
    TF E X → LIB E X k →
    (I • (⊤ : Submodule (𝓞 E) X)).toAddSubgroup.index ≠ 0 ∧
      (I • (⊤ : Submodule (𝓞 E) X)).toAddSubgroup.index ≤ Ideal.absNorm I ^ k := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro I hI hN X _ _ _ htf hli
  by_cases htop : I = ⊤
  · subst htop
    rw [Submodule.top_smul]
    simp
  obtain ⟨P, hPmax, hIP⟩ := Ideal.exists_le_maximal I htop
  obtain ⟨J, rfl⟩ := Ideal.dvd_iff_le.2 hIP
  have hP0 : P ≠ ⊥ := by rintro rfl; exact hI (Ideal.bot_mul J)
  have hJ0 : J ≠ ⊥ := by rintro rfl; exact hI (Ideal.mul_bot P)
  have hNP0 : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hNP1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact hPmax.ne_top
  have hNJ0 : Ideal.absNorm J ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  rw [map_mul] at hN
  have hlt : Ideal.absNorm J < N := by
    rw [← hN]
    have : 1 * Ideal.absNorm J < Ideal.absNorm P * Ideal.absNorm J :=
      Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pos_of_ne_zero hNJ0)
    omega
  obtain ⟨hJ1, hJ2⟩ := ih _ hlt J hJ0 rfl X htf hli
  set L := J • (⊤ : Submodule (𝓞 E) X) with hL
  obtain ⟨hU1, hU2⟩ := index_ideal_smul_top_le_norm_pow P hP0 L k (TF.submodule (h := htf) L) (LIB.submodule (h := hli) L)
  have hle : P • L ≤ L := Submodule.smul_le_right
  have hmul := Formalism.SLP.P.CountO.index_comap_mul (P • L) L hle
  have hcomap : (P • L).comap L.subtype = P • (⊤ : Submodule (𝓞 E) L) := by
    have : (P • (⊤ : Submodule (𝓞 E) L)).map L.subtype = P • L := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
    rw [← this, Submodule.comap_map_eq_of_injective L.injective_subtype]
  rw [hcomap] at hmul
  rw [Submodule.mul_smul, ← hL, ← hmul, map_mul, mul_pow]
  exact ⟨mul_ne_zero hU1 hJ1, Nat.mul_le_mul hU2 hJ2⟩
end Formalism.HermitianLatticeCounting.P
