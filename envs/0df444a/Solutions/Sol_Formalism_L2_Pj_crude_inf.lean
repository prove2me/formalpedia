-- Prove2me | solution 1 for Formalism.L2.Pj.crude_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:20:53.016431+00:00
-- url     : https://prove2.me/submissions/939232c0-9977-4a7d-9a37-bf1a233f20ee

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeDiv
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ConjNeSelfOfCM
import Theorems.Thm_Formalism_L2_Pj_Crude_le_degree
import Theorems.Thm_Formalism_L2_Pj_crude_val
import Theorems.Thm_Formalism_L2_Pj_Crude_diagExp_degree
import Theorems.Thm_Formalism_L2_Pj_Crude_nval_factProd_le
import Theorems.Thm_Formalism_L2_Pj_Crude_nval_factProd_le_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open MvPowerSeries NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} [StarRing (𝓞 E)]
namespace Formalism.L2.Pj
theorem _root_.solution {T : CDVR} {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB T.Fr d O) (h : PS T.Fr 2 d)
    (hg : B.IsCanonGauge T.Fr h) (w0 : O) (k : ℕ) (uvec : Lt1 Dw → Fin d → T.Fr) (hsat : SatDir T uvec)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ha : DomW Dw a) (hn : Fintype.card (Lt1 Dw) ≤ n)
    {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {io : K →+* T.Fr} {e : ℕ}
    (ho : OverLa la T.V io e) :
    crudeInf B h w0 k uvec e a n ≤ (crudeBd la (DF Dw a) : EReal) ∧
      (DF Dw a < resCharOf la → crudeInf B h w0 k uvec e a n ≤ 0) := by
  classical
  obtain ⟨hP, f, hfI, -, hval⟩ := crude_val B h hg w0 k uvec hsat a n ha hn
  have hle : crudeInf B h w0 k uvec e a n ≤ nval T.V e ((fact1 Dw a hn : ℕ) : T.Fr) := by
    unfold crudeInf
    exact iInf_le_of_le (P1 Dw T a hn) (iInf_le_of_le hP (iInf_le_of_le f
      (iInf_le_of_le hfI (by rw [hval]))))
  have hdeg : (Crude.diagExp Dw.mult n (colP Dw hn) (fun τ i => a (τ, i))).degree = DF Dw a := by
    rw [Crude.diagExp_degree]; rfl
  refine ⟨hle.trans ?_, fun hlt => hle.trans ?_⟩
  · have h1 := Crude.nval_factProd_le (ho := ho) (α := Crude.diagExp Dw.mult n (colP Dw hn) (fun τ i => a (τ, i)))
    rw [hdeg] at h1
    exact h1
  · have h2 := Crude.nval_factProd_le_zero (ho := ho) (α := Crude.diagExp Dw.mult n (colP Dw hn) (fun τ i => a (τ, i)))
      (hα := fun s => lt_of_le_of_lt (Crude.le_degree _ s) (hdeg ▸ hlt))
    exact h2
end Formalism.L2.Pj
