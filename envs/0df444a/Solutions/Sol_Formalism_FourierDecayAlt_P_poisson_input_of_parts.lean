-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.poisson_input_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:44:03.252607+00:00
-- url     : https://prove2.me/submissions/ece980e8-3960-45f5-95fa-c5b4f4a849a2

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstNormRealNonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_idl_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_idl_two_le_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_eLat_facts
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_inner_dm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_cj_cemb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_norm_cj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_re_cj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_cj_mp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_first_norm_real_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_ae_allNe
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_dense_allNe
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_idl_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_idl_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_different_power_conj_stable
import Theorems.Thm_Formalism_FourierDecayAlt_P_twistedIsRealOrderLattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C NumberField MeasureTheory
open scoped ComplexOrder ComplexConjugate RealInnerProductSpace
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C.PoissonInputOfParts := by
  intro hEmb hEF hTD _ E _ _ _ Wp Wq _ _ _ _ S hg1 hg2 hP _ hI Kr hK0 Th e
  have hg : 0 < S.g := Nat.mul_pos hg1 hg2
  have hD : ∀ i : ℕ, DiscreteTopology (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1) :=
    fun i => (Cx2.eLat_facts (E := E) hEF S.g hg _).fst
  have hZ : ∀ i : ℕ, IsZLattice ℝ (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1) := by
    intro i
    obtain ⟨_, h⟩ := Cx2.eLat_facts (E := E) hEF S.g hg (S6.nuBlock S.G.r i 1)
    exact h
  obtain ⟨hinj, hbij, _, hsemb, _⟩ := hEmb E
  refine ⟨J.CV E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    InfinitePlace E, inferInstance, J.coord E,
    fun i => J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1, hD, hZ,
    fun _ => J.cemb E, fun _ l => J.dm E S.g 1 (-l), hbij, ?_, ?_⟩
  · intro i _ _
    refine ⟨hinj, ?_, ?_, ?_⟩
    · intro t ht
      have h1 : J.cemb E t = J.semb E 1 t := by rw [hsemb, one_smul]
      rw [h1]
      exact Submodule.mem_map_of_mem (f := (J.semb E 1).toIntLinearMap) ht
    · ext w; simp [J.dm]
    · intro μ hμ
      have hfl := twistedIsRealOrderLattice E (S6.idl E S.g 1 (S6.nuBlock S.G.r i 1))
        (S6.idl E S.g 2 (S6.nuBlock S.G.r i 1)) 1 (Cx2.idl_ne_zero S.g hg 2 _)
        (Cx2.idl_two_le_one S.g _) (different_power_conj_stable E S.g 2 _)
      obtain ⟨l, hl, hlμ⟩ :=
        (hTD E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) S.g 1 hg one_ne_zero hfl.2 μ).1 hμ
      refine ⟨-l, ?_, ?_⟩
      · exact neg_mem hl
      · simpa using hlμ
  · intro ε hε i hi1 hi2 w Y hY κ hκ
    have hi2' : i ≤ S.G.r + 1 := hi2
    obtain ⟨⟨φ, hcont, hext, Cφ, hdec⟩, _⟩ := hI ε hε i hi1 hi2 w Y hY κ hκ
    have hreal : ∀ c, ((φ c).re : ℂ) = φ c ∧ 0 ≤ (φ c).re := by
      have hcl : IsClosed {c : J.CV E | 0 ≤ (φ c).re ∧ (φ c).im = 0} :=
        (isClosed_le continuous_const (Complex.continuous_re.comp hcont)).inter
          (isClosed_eq (Complex.continuous_im.comp hcont) continuous_const)
      have hsub : {c : J.CV E | ∀ v, c (S.pl v) ≠ 0} ⊆
          {c : J.CV E | 0 ≤ (φ c).re ∧ (φ c).im = 0} := by
        intro c hc
        obtain ⟨x, hx, hxe⟩ := Cx2.first_norm_real_nonneg S hP ε hε i hi2 w Y κ hκ c
        rw [Set.mem_ofPred_eq, hext c hc, hxe, Complex.ofReal_re, Complex.ofReal_im]
        exact ⟨hx, rfl⟩
      have hall : ∀ c, 0 ≤ (φ c).re ∧ (φ c).im = 0 := by
        intro c
        have h := closure_minimal hsub hcl
        rw [(Cx2.dense_allNe S).closure_eq] at h
        exact h (Set.mem_univ c)
      intro c
      exact ⟨Complex.ext (by simp) (by simp [(hall c).2]), (hall c).1⟩
    refine ⟨fun c => (φ (Cx2.cj S c)).re, Cφ, Complex.continuous_re.comp (hcont.comp (Cx2.cj S).continuous), ?_,
      fun c => (hreal _).2, ?_, ?_⟩
    · intro c
      refine (Complex.abs_re_le_norm _).trans ((hdec _).trans (le_of_eq ?_))
      congr 1
      exact Fintype.prod_equiv S.pl _ _ (fun v => by simp [J.coord, Cx2.norm_cj])
    · intro t ht
      have hne : ∀ v, (Cx2.cj S (J.cemb E t)) (S.pl v) ≠ 0 := by
        intro v
        rw [Cx2.cj_cemb]
        exact (map_ne_zero (S.σ v)).mpr ht
      have h1 : S.N1 ε i w.1 Y κ (Cx2.cj S (J.cemb E t)) = (S.mkData Kr hK0 Th e).Nst ε i 1 w Y κ t t := by
        simp [HidaSetting.N1, TB.Data.Nst, HidaSetting.mkData, HidaSetting.gram, loc, TB.join, Cx2.cj_cemb, hi2']
      show _ = (φ (Cx2.cj S (J.cemb E t))).re
      rw [hext _ hne, h1]
    · intro l
      show S.Nhat ε i w.1 Y κ l = _
      unfold HidaSetting.Nhat
      congr 1
      rw [integral_congr_ae (g := fun c => φ c * S.psiInf l c)
        ((Cx2.ae_allNe S).mono fun c hc => by simp only [hext c hc])]
      rw [← (Cx2.cj_mp S).integral_comp (Cx2.cj S).toHomeomorph.measurableEmbedding
        (fun c => φ c * S.psiInf l c)]
      rw [Real.fourier_eq]
      congr 1
      funext c
      rw [(hreal (Cx2.cj S c)).1, Circle.smul_def, smul_eq_mul, mul_comm]
      congr 1
      unfold HidaSetting.psiInf
      rw [Real.fourierChar_apply, Cx2.inner_dm]
      have hs : (∑ v : Fin S.f, 2 * (S.σ v l * (Cx2.cj S c) (S.pl v)).re) =
          ∑ w : InfinitePlace E, 2 * (w.embedding l * c w).re :=
        Fintype.sum_equiv S.pl _ _ (fun v => by rw [Cx2.re_cj])
      rw [hs]
      congr 1
      push_cast
      ring
end Formalism.FourierDecayAlt.P
