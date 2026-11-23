-- Prove2me | solution 1 for Formalism.HN.twist_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:25.687794+00:00
-- url     : https://prove2.me/submissions/360ff1c2-bdfb-4d98-b4d4-0586c318968a

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TwistFinrankEq
import Theorems.Thm_Formalism_HN_twist_finrank_eq
import Theorems.Thm_Formalism_F_covol_pos


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
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution (h1 : RescaleCovol) (h2 : PlLat) (h3 : ShiftInvariance.{0, 0, 0, 0}) : Twist := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X c hX hc
  dsimp only
  intro L hL
  have hX' : ∀ v, IsUnit (((c v : ℂ)) • X v).det := by
    intro v
    rw [Matrix.det_smul]
    exact ((isUnit_iff_ne_zero.mpr (by exact_mod_cast (hc v).ne' : ((c v : ℂ)) ≠ 0)).pow _).mul (hX v)
  have hfg : ∀ N : Submodule (𝓞 K) V, N ≤ L → N.FG := by
    intro N hN
    haveI := isNoetherian_of_fg_of_noetherian L hL
    have h1' : (N.comap L.subtype).FG := IsNoetherian.noetherian _
    have h2' := h1'.map L.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hN] at h2'
  have hnPl : (nPl K : ℝ) ≠ 0 := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this.ne'
  have hfr := twist_finrank_eq K
  have hP : 0 < ∏ v, c v := Finset.prod_pos fun v _ => hc v
  have hlogP : Real.log (∏ v, c v) = ∑ v, Real.log (c v) := Real.log_prod fun v _ => (hc v).ne'
  have hkey : ∀ N : Submodule (𝓞 K) V, N ≤ L →
      rk (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) N = rk (Formalism.HermitianLatticesTheory.realize b X) N ∧
      deg (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) N = deg (Formalism.HermitianLatticesTheory.realize b X) N +
        (1 / (nPl K : ℝ)) * (∑ v, Real.log (c v)) * (rk (Formalism.HermitianLatticesTheory.realize b X) N : ℝ) := by
    intro N hN
    have hNfg := hfg N hN
    obtain ⟨hlat, hrk, -⟩ := h2 K V ι b X hX N hNfg
    obtain ⟨-, hrk₂, -⟩ := h2 K V ι b (fun v => ((c v : ℂ)) • X v) hX' N hNfg
    refine ⟨by rw [hrk, hrk₂], ?_⟩
    have hcov := h1 K V ι b X c hX hc N hNfg
    haveI := hlat.2
    have hC := Formalism.F.covol_pos (zl (Formalism.HermitianLatticesTheory.realize b X) N)
    simp only [deg, Formalism.F.deg]
    rw [hcov, Real.log_mul (Real.rpow_pos_of_pos hP _).ne' hC.ne', Real.log_rpow hP, hlogP, hrk]
    push_cast
    rw [hfr]
    field_simp
    ring
  obtain ⟨hlatL, hrkL, -⟩ := h2 K V ι b X hX L hL
  obtain ⟨hlatL₂, -, -⟩ := h2 K V ι b (fun v => ((c v : ℂ)) • X v) hX' L hL
  obtain ⟨-, hmu, hstep, -⟩ := h3 (𝓞 K) V _ _ (Formalism.HermitianLatticesTheory.realize b X)
    (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) L ((1 / (nPl K : ℝ)) * ∑ v, Real.log (c v))
    hlatL hlatL₂ hkey
  have hrkpos : L ≠ ⊥ → (rk (Formalism.HermitianLatticesTheory.realize b X) L : ℝ) ≠ 0 := by
    intro hne
    rw [hrkL]
    have h1' : 0 < Module.finrank ℚ K := Module.finrank_pos
    have h2' : 0 < rkK L := by
      obtain ⟨s, hs⟩ := hL
      unfold rkK
      rw [← hs, Submodule.span_span_of_tower (𝓞 K) K (s : Set V)]
      haveI : FiniteDimensional K (Submodule.span K (s : Set V)) := FiniteDimensional.span_finset K s
      rw [Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot]
      intro h0
      apply hne
      rw [← hs, eq_bot_iff]
      intro x hx
      have hx' := Submodule.span_le_restrictScalars (𝓞 K) K (s : Set V) hx
      have hx0 : x = 0 := by simpa [h0] using hx'
      simp [hx0]
    exact_mod_cast (Nat.mul_pos h1' h2').ne'
  have hslope : L ≠ ⊥ → slope (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) L =
      slope (Formalism.HermitianLatticesTheory.realize b X) L + (1 / (nPl K : ℝ)) * ∑ v, Real.log (c v) := by
    intro hne
    have hs : ∀ ρ' : V →+ EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2),
        slope ρ' L = deg ρ' L / (rk ρ' L : ℝ) := fun _ => rfl
    rw [hs, hs, (hkey L le_rfl).1, (hkey L le_rfl).2, add_div, mul_div_assoc, div_self (hrkpos hne),
      mul_one]
  refine ⟨hslope, hmu, fun hne => ?_, fun θ => hstep θ⟩
  simp only [muDef, muMaxDef, muMinDef, hslope hne, (hmu hne).1, (hmu hne).2]
  refine ⟨by ring, by ring, by ring⟩
end Formalism.HN
