-- Prove2me | solution 1 for Formalism.ExtensionFiltration.slope_image_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:40:29.978609+00:00
-- url     : https://prove2.me/submissions/e91c19b0-4613-4ce5-bc46-7ae86cb8ac93

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeIneq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_DescentSlope
import Theorems.Thm_Formalism_HN_height_image_formula
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_saturation_basic_properties
import Theorems.Thm_Formalism_HN_sizeIneq_rk
import Theorems.Thm_Formalism_HN_size_maximal_slope


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
namespace Formalism.ExtensionFiltration
theorem _root_.solution
    {K V ι W κ : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ)
    (hX : ∀ v, IsUnit (X v).det) (hX' : ∀ v, IsUnit (X' v).det)
    (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) (hAfg : A.FG) (hA0 : A ≠ ⊥)
    (hinj : Function.Injective φ) :
    rkK (A.map (φ.restrictScalars (𝓞 K))) = rkK A ∧
      2 * slope (Formalism.HermitianLatticesTheory.realize b X) A - htMap b X b' X' φ ≤
        2 * slope (Formalism.HermitianLatticesTheory.realize b' X') (A.map (φ.restrictScalars (𝓞 K))) := by
  have : FiniteDimensional K V := Module.Finite.of_basis b
  have hrkeq := sizeIneq_rk φ A
  obtain ⟨hsat, hht⟩ := height_image_formula K V ι W κ b X b' X' hX hX' φ A hAfg
  have hker : A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) = ⊥ := by
    rw [LinearMap.ker_eq_bot.2 hinj, Submodule.restrictScalars_bot, inf_bot_eq]
  rw [hker] at hrkeq hsat hht
  have hrkbot : rkK (K := K) (⊥ : Submodule (𝓞 K) V) = 0 := by
    unfold rkK
    simp
  rw [hrkbot, add_zero] at hrkeq
  refine ⟨hrkeq, ?_⟩
  set I := A.map (φ.restrictScalars (𝓞 K)) with hIdef
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set ρ' := Formalism.HermitianLatticesTheory.realize b' X' with hρ'
  have hIfg : I.FG := hAfg.map _
  have hI0 : I ≠ ⊥ := by
    intro h
    apply hA0
    rw [eq_bot_iff]
    intro x hx
    have hm : φ x ∈ I := ⟨x, hx, rfl⟩
    rw [h] at hm
    have h0 : φ x = 0 := (Submodule.mem_bot _).1 hm
    exact (Submodule.mem_bot _).2 (hinj (by rw [h0, map_zero]))
  obtain ⟨hAlat, -, -⟩ := place_lattice_structure K V ι b X hX A hAfg
  obtain ⟨-, -, hhtI⟩ := place_lattice_structure K W κ b' X' hX' I hIfg
  obtain ⟨-, -, hsQ, -, -, -⟩ := size_maximal_slope K V ι b X hX A hAfg hA0
  have hSI := (size_maximal_slope K W κ b' X' hX' I hIfg hI0).1
  have hSBA := saturation_basic_properties (𝓞 K) V _ ρ A hAlat
  have hq := hSBA.2.2.2.2.2.2.2 ⊥ hsat
  have hrb : rk ρ (⊥ : Submodule (𝓞 K) V) = 0 := (hSBA.2.2.2.1 ⊥ bot_le).2 rfl
  have hdb : deg ρ (⊥ : Submodule (𝓞 K) V) = 0 := hSBA.2.2.2.2.1
  have hslQ : Formalism.F.slope (Formalism.F.quot (zl ρ A) (zl ρ (⊥ : Submodule (𝓞 K) V))) = slope ρ A := by
    unfold Formalism.F.slope
    rw [hq.1, hq.2.2, hrb, hdb, Nat.sub_zero, sub_zero]
    rfl
  have hsQ' := hsQ ⊥ hsat (Ne.symm hA0)
  rw [hslQ] at hsQ'
  set P := ∏ v, opNormAt b X b' X' v φ with hPdef
  have hP : 0 ≤ P := Finset.prod_nonneg (fun v _ => norm_nonneg _)
  have hf : (0 : ℝ) < nPl K := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this
  have hs : (0 : ℝ) < rkK I := by
    rw [hrkeq]
    have h : Submodule.span K (A : Set V) ≠ ⊥ := by
      intro h
      apply hA0
      rw [Submodule.span_eq_bot] at h
      exact (Submodule.eq_bot_iff _).2 (fun x hx => h x hx)
    have : 0 < rkK (K := K) A :=
      Nat.lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.2 h)
    exact_mod_cast this
  have hrkR : ((rkK A : ℝ) - rkK (K := K) (⊥ : Submodule (𝓞 K) V)) = rkK I := by
    rw [hrkbot, hrkeq]; simp
  rw [Finset.prod_pow, ← hPdef] at hht
  have hX0 : 0 ≤ P ^ (2 * rkK I) := pow_nonneg hP _
  have hQpos : 0 < htQ b X A ⊥ := pos_of_mul_pos_right (lt_of_lt_of_le hhtI hht) hX0
  have hPpos : 0 < P := by
    rcases hP.lt_or_eq with h | h
    · exact h
    · exfalso
      have hne : 2 * rkK I ≠ 0 := by
        have : 0 < rkK I := by exact_mod_cast hs
        omega
      rw [← h, zero_pow hne, zero_mul] at hht
      exact absurd hhtI (not_lt.2 hht)
  have he : (0 : ℝ) ≤ 1 / (2 * (nPl K : ℝ) * (rkK I : ℝ)) := by positivity
  have hcore : size b' X' I ≤ P ^ ((1 : ℝ) / (nPl K : ℝ)) * sizeQ b X A ⊥ := by
    unfold size sizeQ
    rw [hrkR]
    calc ht b' X' I ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ)))
        ≤ (P ^ (2 * rkK I) * htQ b X A ⊥) ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) :=
          Real.rpow_le_rpow hhtI.le hht he
      _ = (P ^ (2 * rkK I)) ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) *
            htQ b X A ⊥ ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) :=
          Real.mul_rpow hX0 hQpos.le
      _ = P ^ ((1 : ℝ) / (nPl K : ℝ)) *
            htQ b X A ⊥ ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) := by
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hP]
          congr 1
          push_cast
          field_simp
  rw [hSI, hsQ', Real.rpow_def_of_pos hPpos, ← Real.exp_add, Real.exp_le_exp] at hcore
  have hht2 : htMap b X b' X' φ = 2 * (Real.log P * (1 / (nPl K : ℝ))) := by
    unfold htMap
    have hne : ∀ v ∈ (Finset.univ : Finset (InfinitePlace K)), opNormAt b X b' X' v φ ≠ 0 := by
      intro v hv h0
      exact hPpos.ne' (Finset.prod_eq_zero hv h0)
    rw [hPdef, Real.log_prod hne]
    simp only [Real.log_pow]
    rw [← Finset.mul_sum]
    push_cast
    ring
  rw [hht2]
  linarith
end Formalism.ExtensionFiltration
