-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RawChart.F_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:06:07.869668+00:00
-- url     : https://prove2.me/submissions/4f655f88-3947-444c-8a0b-fa465761f7d2

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_ge_of_pow_eq_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_unV_mem
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_sum_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_teich_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
namespace Formalism.L2.FormalSeriesBounds.RawChart
theorem _root_.solution (V : VF C) (g : Fin 2) (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    {ζ : C} (hζ : IsPrimitiveRoot ζ V.l)
    (h0 : (0 : ℕ → I g ⊕ JJ I g → C) ∈ X.TySet V g)
    (hadd : ∀ x y, x ∈ X.TySet V g → y ∈ X.TySet V g → x + y ∈ X.TySet V g)
    (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) : Fs V.l x ∈ X.TySet V g := by
  have hl2 := V.l_prime.two_le
  apply X.unV_mem V g hlg0 hexlg hζ
  have hsum : ∑ k ∈ Finset.range V.l, teich V.l (ζ ^ k) x ∈ X.TySet V g :=
    X.sum_mem V g h0 hadd _ _ fun k _ =>
      X.teich_mem V g _ ((V.ge_of_pow_eq_one (by omega) hζ.pow_eq_one).pow k) x hx
  have e : ∑ k ∈ Finset.range V.l, teich V.l (ζ ^ k) x = Vpow 1 (Fs V.l x) := by
    funext i n
    rw [Finset.sum_apply, Finset.sum_apply]
    show ∑ k ∈ Finset.range V.l, (ζ ^ k) ^ (V.l ^ i) * x i n = if i < 1 then 0 else (V.l : C) * x (i - 1 + 1) n
    rw [← Finset.sum_mul]
    cases i with
    | zero =>
      simp only [pow_zero, pow_one]
      rw [hζ.geom_sum_eq_zero (by omega), zero_mul]
      simp
    | succ i =>
      have h1 : ∀ k, (ζ ^ k) ^ (V.l ^ (i + 1)) = 1 := by
        intro k
        rw [← pow_mul, mul_comm, pow_mul, pow_succ', pow_mul, hζ.pow_eq_one, one_pow, one_pow]
      simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      simp
  rwa [e] at hsum
end Formalism.L2.FormalSeriesBounds.RawChart
