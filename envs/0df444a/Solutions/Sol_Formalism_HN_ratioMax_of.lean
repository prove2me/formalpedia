-- Prove2me | solution 1 for Formalism.HN.ratioMax_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:11.229396+00:00
-- url     : https://prove2.me/submissions/712b3459-4e3c-4e66-9857-a1b7e86ce2af

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Theorems.Thm_Formalism_HN_le_of_imageLattice_le
import Theorems.Thm_Formalism_F_covol_pos
import Theorems.Thm_Formalism_F_finiteSaturated
import Theorems.Thm_Formalism_F_saturProps
import Theorems.Thm_Formalism_HN_satBasic_zl_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe u v w
namespace Formalism.HN
theorem _root_.solution (h1 : SatR.{u, v, w}) (h2 : SatBasic.{u, v, w}) : RatioMax.{u, v, w} := by
  unfold RatioMax
  intro R V E _ _ _ _ _ _ ρ L S hL hS hSL
  obtain ⟨hsub, hmono, hsat, -, -, -, hLsat, -⟩ := h2 R V E ρ L hL
  have hinj : Set.InjOn ρ (L : Set V) := hL.1
  have hdL : DiscreteTopology (zl ρ L) := hL.2
  have hSle : S ≤ L := hS.1
  have hSL' : S < L := lt_of_le_of_ne hSle hSL
  have hgap : ∀ N : Submodule R V, S < N → N ≤ L → (rk ρ S : ℝ) < rk ρ N := by
    intro N hSN hNL
    have hle := (hmono S N hSN.le hNL).1
    have hne : rk ρ N ≠ rk ρ S := fun he => hSN.ne (hsat S N hS hSN.le hNL he).symm
    exact_mod_cast lt_of_le_of_ne hle (Ne.symm hne)
  obtain ⟨f, hf⟩ : ∃ f : Submodule R V → ℝ, ∀ N, f N =
      (deg ρ N - deg ρ S) / ((rk ρ N : ℝ) - rk ρ S) := ⟨_, fun _ => rfl⟩
  have hdeg : ∀ N : Submodule R V, S < N → N ≤ L → f L ≤ f N →
      deg ρ S - |f L| * (rk ρ L : ℝ) ≤ deg ρ N := by
    intro N hSN hNL hc
    have hpos : 0 < (rk ρ N : ℝ) - rk ρ S := sub_pos.2 (hgap N hSN hNL)
    have hrN : (rk ρ N : ℝ) - rk ρ S ≤ rk ρ L := by
      have h3 : (rk ρ N : ℝ) ≤ rk ρ L := by exact_mod_cast (hmono N L hNL le_rfl).1
      have h4 : (0 : ℝ) ≤ rk ρ S := Nat.cast_nonneg _
      linarith
    rw [hf N, le_div_iff₀ hpos] at hc
    have h3 : -|f L| * (rk ρ L : ℝ) ≤ f L * ((rk ρ N : ℝ) - rk ρ S) := by
      calc -|f L| * (rk ρ L : ℝ) ≤ -|f L| * ((rk ρ N : ℝ) - rk ρ S) :=
            mul_le_mul_of_nonpos_left hrN (neg_nonpos.2 (abs_nonneg _))
        _ ≤ f L * ((rk ρ N : ℝ) - rk ρ S) :=
            mul_le_mul_of_nonneg_right (neg_abs_le _) hpos.le
    linarith
  obtain ⟨T, hTdef⟩ : ∃ T : Set (Submodule R V),
      T = {N | IsSat ρ L N ∧ S < N ∧ f L ≤ f N} := ⟨_, rfl⟩
  have hmemT : ∀ N, N ∈ T ↔ IsSat ρ L N ∧ S < N ∧ f L ≤ f N := by
    intro N
    subst hTdef
    exact Iff.rfl
  have hfinE := Formalism.F.finiteSaturated E (zl ρ L) hdL
      (Real.exp (-(deg ρ S - |f L| * (rk ρ L : ℝ))))
  have hT : T.Finite := by
    refine Set.Finite.of_finite_image (f := zl ρ) (hfinE.subset ?_) ?_
    · rintro _ ⟨N, hN, rfl⟩
      obtain ⟨hNs, hSN, hc⟩ := (hmemT N).1 hN
      show _ ∧ _
      refine ⟨hNs.2, ?_⟩
      have hlat := hsub N hNs.1
      have : DiscreteTopology (zl ρ N) := hlat.2
      have hcpos : 0 < Formalism.F.covol (zl ρ N) :=
        Formalism.F.covol_pos _
      have hd := hdeg N hSN hNs.1 hc
      have hdN : deg ρ N = -Real.log (Formalism.F.covol (zl ρ N)) := rfl
      rw [← Real.log_le_iff_le_exp hcpos]
      linarith
    · intro A hA B hB hAB
      have hA' := ((hmemT A).1 hA).1.1
      have hB' := ((hmemT B).1 hB).1.1
      exact le_antisymm
        (le_of_imageLattice_le ρ L A B hinj hA' hB' hAB.le)
        (le_of_imageLattice_le ρ L B A hinj hB' hA' hAB.ge)
  have hLT : L ∈ T := (hmemT L).2 ⟨hLsat, hSL', le_rfl⟩
  obtain ⟨N, hNT, hNmax⟩ := Set.exists_max_image T f hT ⟨L, hLT⟩
  obtain ⟨hNsat, hSN, -⟩ := (hmemT N).1 hNT
  refine ⟨N, hSN, hNsat, ?_⟩
  intro N' hSN' hN'L
  have hpos' : 0 < (rk ρ N' : ℝ) - rk ρ S := sub_pos.2 (hgap N' hSN' hN'L)
  have hposN : 0 < (rk ρ N : ℝ) - rk ρ S := sub_pos.2 (hgap N hSN hNsat.1)
  have key : f N' ≤ f N := by
    by_cases hc : f L ≤ f N'
    · obtain ⟨N'', hle, hN''L, himg⟩ := h1 R V E ρ L N' hL hN'L
      have hmon : zl ρ N' ≤ zl ρ L := satBasic_zl_mono ρ hN'L
      have hsp := Formalism.F.saturProps E (zl ρ L) (zl ρ N')
        hdL hmon
      have hsat'' : IsSat ρ L N'' := by
        refine And.intro hN''L ?_
        rw [himg]
        exact hsp.1
      have hrk : rk ρ N'' = rk ρ N' := by
        show Formalism.F.rk (zl ρ N'') = Formalism.F.rk (zl ρ N')
        rw [himg]
        exact hsp.2.2
      have hdg : deg ρ N' ≤ deg ρ N'' := (hmono N' N'' hle hN''L).2 hrk.symm
      have hff : f N' ≤ f N'' := by
        rw [hf N', hf N'', hrk, div_le_div_iff₀ hpos' hpos']
        exact mul_le_mul_of_nonneg_right (by linarith) hpos'.le
      have hN''T : N'' ∈ T := (hmemT N'').2 ⟨hsat'', lt_of_lt_of_le hSN' hle, hc.trans hff⟩
      exact hff.trans (hNmax N'' hN''T)
    · have hlt : f N' < f L := not_le.1 hc
      exact hlt.le.trans ((hmemT N).1 hNT).2.2
  rw [hf N', hf N, div_le_div_iff₀ hpos' hposN] at key
  exact key
end Formalism.HN
