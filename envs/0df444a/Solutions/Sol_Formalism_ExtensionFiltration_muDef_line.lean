-- Prove2me | solution 1 for Formalism.ExtensionFiltration.muDef_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:41:28.859106+00:00
-- url     : https://prove2.me/submissions/d6d398ce-7e53-403c-a355-b73a738d2338

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_SpanMuMin
import Theorems.Thm_Formalism_ExtensionFiltration_majAt_self_re
import Theorems.Thm_Formalism_ExtensionFiltration_rkK_span_singleton
import Theorems.Thm_Formalism_HN_height_gram_determinant
import Theorems.Thm_Formalism_HN_place_lattice_structure
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
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
  [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.ExtensionFiltration
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : x ≠ 0) (Λ : ℝ)
    (hn : ∀ v, Formalism.HermitianLatticesTheory.normAt b X v x ≤ Real.exp Λ) :
    -(2 * Λ) ≤ muDef b X (Submodule.span (𝓞 K) ({x} : Set V)) := by
  classical
  set L := Submodule.span (𝓞 K) ({x} : Set V) with hLdef
  have hFG : L.FG := Submodule.fg_span_singleton x
  have hne : L ≠ ⊥ := by
    rw [hLdef, Ne, Submodule.span_singleton_eq_bot]
    exact hx
  obtain ⟨-, -, hpos⟩ := Formalism.HN.place_lattice_structure K V ι b X hX L hFG
  have hmu := (Formalism.HN.size_maximal_slope K V ι b X hX L hFG hne).2.1
  have hli : LinearIndependent K ![x] := linearIndependent_unique_iff.mpr (by simpa using hx)
  have hr : Set.range ![x] = ({x} : Set V) := by
    rw [Set.range_unique]
    simp
  obtain ⟨hht, -⟩ := Formalism.HN.height_gram_determinant K V ι b X hX 1 ![x] hli
  rw [hr] at hht
  have hg : ∀ v, (gramPl b X v ![x]).det.re = Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 := by
    intro v
    rw [Matrix.det_unique]
    exact majAt_self_re b X v x
  simp only [hg] at hht
  have hrk : rkK (K := K) L = 1 := rkK_span_singleton x hx
  have hnPl : 0 < nPl K := Fintype.card_pos
  have hle : ht b X L ≤ (Real.exp Λ ^ 2) ^ nPl K := by
    rw [hht]
    calc ∏ v, Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 ≤ ∏ _v : InfinitePlace K, Real.exp Λ ^ 2 :=
          Finset.prod_le_prod (fun v _ => by positivity)
            (fun v _ => pow_le_pow_left₀ (by unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm; exact Real.sqrt_nonneg _)
              (hn v) 2)
      _ = (Real.exp Λ ^ 2) ^ nPl K := by rw [Finset.prod_const, Finset.card_univ]; rfl
  have hlog : Real.log (ht b X L) ≤ (nPl K : ℝ) * (2 * Λ) := by
    have h1 := Real.log_le_log hpos hle
    rwa [Real.log_pow, Real.log_pow, Real.log_exp] at h1
  rw [hmu]
  unfold size
  rw [hrk, Real.log_rpow hpos]
  have hn' : (0 : ℝ) < nPl K := by exact_mod_cast hnPl
  have key : 1 / (2 * (nPl K : ℝ) * ((1 : ℕ) : ℝ)) * Real.log (ht b X L) ≤ Λ := by
    rw [Nat.cast_one, mul_one, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  linarith
end Formalism.ExtensionFiltration
