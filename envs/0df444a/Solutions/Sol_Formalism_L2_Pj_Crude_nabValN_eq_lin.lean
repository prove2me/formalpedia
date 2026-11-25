-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.nabValN_eq_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:52:56.62545+00:00
-- url     : https://prove2.me/submissions/98b1de6a-ae07-458a-9061-3c2a6dbeec3f

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
import Theorems.Thm_Formalism_L2_Pj_Crude_ordGe_one_iff
import Theorems.Thm_Formalism_L2_Pj_Crude_OrdGe_mul
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_ordGe_zero
import Theorems.Thm_P2M_Formalism_L2_Pj_Crude_cro_ordGe_zero__ecad83ed03f0
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_ordGe_lin
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_constCoeff_ev
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_constCoeff_expS
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_coeff_lin
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_word_const
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_lin_sub
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_dofN_sub
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_ordGe_dofN
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_dofN_lin

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
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution [Algebra ℚ k] {O : Type} [CommRing O] [StarRing O] (B : FB k d O) (h : PS k 2 d)
    (hg : B.IsCanonGauge k h) (w0 : O) (m : ℕ) (f : PS k n d) {ι : Type} [Fintype ι] (cp : ι → Fin n)
    (u : ι → Fin d → k) (P : MvPolynomial ι k) (N : ℕ) (hP : ∀ a ∈ P.support, a.degree = N)
    (hf : OrdGe N f) :
    nabValN B k h w0 m f cp u P = ∑ a ∈ P.support, P.coeff a * constantCoeff (LinMon cp u a f) := by
  classical
  have hpt : ∀ {n' : ℕ} (b : Fin n') (i : Fin d), constantCoeff (pt k d b i : PS k n' d) = 0 := by
    intro n' b i; simp [pt]
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hg.ax0
    rw [cro_constCoeff_ev] at this
    · simpa using this
    · intro p i; fin_cases p
      · simp
      · exact hpt 0 i
  have hL0 : constantCoeff (B.hL k h w0) = 0 := by
    unfold FB.hL
    rw [cro_constCoeff_ev, hh0]
    intro p i
    fin_cases p
    · exact hpt 0 i
    · show constantCoeff (comp1 (B.actK k w0) (pt k d 0) i) = 0
      unfold comp1
      rw [cro_constCoeff_ev]
      · simp [FB.actK, B.A.const]
      · intro p i'; fin_cases p; exact hpt 0 i'
  set g := FB.expS k ((m : k) • ∑ b : Fin n, ev (n := n) ![pt k d b] (B.hL k h w0)) with hg_def
  have hg1 : constantCoeff g = 1 := by
    apply cro_constCoeff_expS
    rw [smul_eq_C_mul, map_mul, map_sum]
    have : ∀ b : Fin n, constantCoeff (ev (n := n) ![pt k d b] (B.hL k h w0)) = 0 := by
      intro b
      rw [cro_constCoeff_ev, hL0]
      intro p i; fin_cases p; exact hpt b i
    simp [this]
  have hFK : ∀ i j, coeff (Finsupp.single ((1 : Fin 2), i) 1) (B.FK k j) = if i = j then 1 else 0 := by
    intro i j
    simp only [FB.FK, FGLaw.mapF, coeff_map, cro_coeff_lin, Algebra.algebraMap_self, RingHom.id_apply]
  unfold nabValN DpolyN
  rw [map_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [map_mul, constantCoeff_C]
  congr 1
  have hfa : OrdGe a.degree f := (hP a ha) ▸ hf
  have hfg : OrdGe a.degree (f * g) := by simpa using hfa.mul (cro_ordGe_zero g)
  have hg' : OrdGe 1 (g - 1) := (ordGe_one_iff _).2 (by rw [map_sub, hg1, map_one, sub_self])
  have hdiff : OrdGe (a.degree + 1) (f * g - f) := by
    have : f * g - f = f * (g - 1) := by ring
    rw [this]; exact hfa.mul hg'
  have s1 := cro_word_const (fun l => DofN (B.FK k) (cp l) (u l)) (fun l => Lin (cp l) (u l)) a
    (fun l X Y => cro_dofN_sub _ _ _ X Y) (fun l t X hX => cro_ordGe_dofN _ _ _ hX)
    (fun l t X hX => cro_ordGe_lin hX _ _) (fun l t X hX => cro_dofN_lin _ hFK _ _ hX) (f * g) (f * g)
    hfg hfg (by rw [sub_self]; exact cro_ordGe_zero' _)
  have s2 := cro_word_const (fun l => Lin (cp l) (u l)) (fun l => Lin (cp l) (u l)) a
    (fun l X Y => cro_lin_sub _ _ X Y) (fun l t X hX => cro_ordGe_lin hX _ _)
    (fun l t X hX => cro_ordGe_lin hX _ _) (fun l t X hX => by rw [sub_self]; exact cro_ordGe_zero' _)
    (f * g) f hfg hfa hdiff
  unfold DmonN LinMon
  exact s1.trans s2
end Formalism.L2.Pj.Crude
