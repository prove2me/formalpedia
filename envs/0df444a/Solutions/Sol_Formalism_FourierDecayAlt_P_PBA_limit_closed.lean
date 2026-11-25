-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.limit_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:53:07.997173+00:00
-- url     : https://prove2.me/submissions/ff3bf631-9de6-47eb-b6b5-e30dd93ea8a3

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalNormNonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_extract_prob
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_nst_tendsto
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_base_count_tendsto
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_local_norm_nonneg_alt
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt NumberField
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution : KB.LimitClosed := by
  intro E _ _ _ Wp Wq _ _ _ _ S RR hconv
  refine ⟨?_, ?_, ?_⟩
  · intro Λ hL ε hε i s hs hsi hir w hw hcnt
    choose θn hθn hbd using fun n => hL n ε hε i s hs hsi hir w hw hcnt
    obtain ⟨φ, θ, hφ, hθ, hlim⟩ := extract_prob (ι := Finset (Fin S.f)) (X := S.W × S.W)
      (S.base.Wb (S.base.cnt w + S.base.K) ×ˢ S.base.Wb (S.base.cnt w + S.base.K)) (fun n => θn n) hθn
    refine ⟨θ, hθ, ?_⟩
    intro Y T κ hY hκ t ht t' ht' h0 h0' ho A
    have h1 : ∀ n, (∏ v ∈ A, S.base.av v (t⁻¹ - t'⁻¹) ^ S.base.K) *
        ‖(KB.withRR S (RR (φ n))).base.Nst ε i s w Y (TB.blk κ s t t') t t'‖ ≤
        (∏ v ∈ A, Λ (i - s + 1) s v ^ S.base.K) *
          ∑ x ∈ S.base.Wb (S.base.cnt w + S.base.K) ×ˢ S.base.Wb (S.base.cnt w + S.base.K), θn (φ n) A x *
            ((((KB.withRR S (RR (φ n))).base.Nst ε i s x.1 Y (TB.blk κ s t t) t t).re +
              ((KB.withRR S (RR (φ n))).base.Nst ε i s x.2 Y (TB.blk κ s t' t') t' t').re) / 2) :=
      fun n => hbd (φ n) Y T κ hY hκ t ht t' ht' h0 h0' ho A
    refine le_of_tendsto_of_tendsto' (b := (atTop : Filter ℕ)) ?_ ?_ h1
    · exact tendsto_const_nhds.mul ((nst_tendsto hconv hε i s w Y _ t t').comp hφ.tendsto_atTop).norm
    · refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun x hx => (hlim A x hx).mul ?_)
      refine Tendsto.div_const (Tendsto.add ?_ ?_) _
      · exact (Complex.continuous_re.tendsto _).comp ((nst_tendsto hconv hε i s x.1 Y _ t t).comp hφ.tendsto_atTop)
      · exact (Complex.continuous_re.tendsto _).comp
          ((nst_tendsto hconv hε i s x.2 Y _ t' t').comp hφ.tendsto_atTop)
  · intro Λ' hL ε hε s hs hsr w hw hcnt
    choose θn hθn hbd using fun n => hL n ε hε s hs hsr w hw hcnt
    obtain ⟨φ, θ, hφ, hθ, hlim⟩ := extract_prob (ι := Finset (Fin S.f)) (X := S.W)
      (S.base.Wb (S.base.cnt w + S.base.K)) (fun n => θn n) hθn
    refine ⟨θ, hθ, ?_⟩
    intro Y hY κ hκ t ht B
    have h1 : ∀ n, ((KB.withRR S (RR (φ n))).base.Nst ε (S.G.r + 1) s w Y κ t t).re ≤
        (∏ v ∈ B, (S.base.av v t * Λ' (S.G.r + 2 - s) s v) ^ (2 * S.base.K)) *
          ∑ w' ∈ S.base.Wb (S.base.cnt w + S.base.K), θn (φ n) B w' *
            ((KB.withRR S (RR (φ n))).base.Nst ε (S.G.r + 1) s w' Y κ t t).re :=
      fun n => hbd (φ n) Y hY κ hκ t ht B
    refine le_of_tendsto_of_tendsto' (b := (atTop : Filter ℕ)) ?_ ?_ h1
    · exact (Complex.continuous_re.tendsto _).comp
        ((nst_tendsto hconv hε (S.G.r + 1) s w Y κ t t).comp hφ.tendsto_atTop)
    · refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun x hx => (hlim B x hx).mul ?_)
      exact (Complex.continuous_re.tendsto _).comp
        ((nst_tendsto hconv hε (S.G.r + 1) s x Y κ t t).comp hφ.tendsto_atTop)
  · intro C₄ hP _ hSF ε hε i s hs hsi hir w hw hcnt hvol
    set Bd := C₄ ^ (S.base.f * s) * (∏ s' ∈ Ico 1 s, S.base.vol (i - s + 1) s')
    have H : ∀ n, ∃ θ : Unit → S.W → ℝ, (∀ u, TB.IsProb (S.base.Wb (S.base.cnt w + s * S.base.K)) (θ u)) ∧
        ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - s) → ∀ κ, TB.PSDOn Y κ →
          ∀ (t₀ : E) (T : Finset E), (∀ t ∈ T, t ≠ 0 ∧ t - t₀ ∈ S.base.La (i - s + 1) s) →
            ∑ t ∈ T, ((KB.withRR S (RR n)).base.Nst ε i s w Y κ t t).re ≤
              Bd * ∑ w' ∈ S.base.Wb (S.base.cnt w + s * S.base.K), θ () w' *
                (KB.withRR S (RR n)).base.N0 ε (i - s) w' Y κ := by
      intro n
      obtain ⟨Mv, hMv, θ, hθ, hb⟩ := hSF n ε hε i s hs hsi hir w hw hcnt hvol
      refine ⟨fun _ => θ, fun _ => hθ, ?_⟩
      intro Y hY κ hκ t₀ T hT
      refine (hb Y hY κ hκ t₀ T hT).trans ?_
      apply mul_le_mul_of_nonneg_right hMv
      exact Finset.sum_nonneg fun w' _ => mul_nonneg (hθ.1 w') (local_norm_nonneg_alt (hP n) hε _ w' Y κ hκ)
    choose θn hθn hbd using H
    obtain ⟨φ, θ, hφ, hθ, hlim⟩ := extract_prob _ θn hθn
    refine ⟨Bd, le_refl _, θ (), hθ (), ?_⟩
    intro Y hY κ hκ t₀ T hT
    have h1 : ∀ n, ∑ t ∈ T, ((KB.withRR S (RR (φ n))).base.Nst ε i s w Y κ t t).re ≤
        Bd * ∑ w' ∈ S.base.Wb (S.base.cnt w + s * S.base.K), θn (φ n) () w' *
          (KB.withRR S (RR (φ n))).base.N0 ε (i - s) w' Y κ := fun n => hbd (φ n) Y hY κ hκ t₀ T hT
    refine le_of_tendsto_of_tendsto' (b := (atTop : Filter ℕ)) ?_ ?_ h1
    · exact tendsto_finsetSum _ fun t _ => (Complex.continuous_re.tendsto _).comp
        ((nst_tendsto hconv hε i s w Y κ t t).comp hφ.tendsto_atTop)
    · refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun x hx => (hlim () x hx).mul ?_)
      exact (base_count_tendsto hconv hε (i - s) x Y κ).comp hφ.tendsto_atTop
end Formalism.FourierDecayAlt.P.PBA
