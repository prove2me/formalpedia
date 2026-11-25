-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.top_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:57:26.411794+00:00
-- url     : https://prove2.me/submissions/a83a5f0c-d6b7-4a72-937e-97710c88e292

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SizeAtNonneg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopOfLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_BaseGramNonnegativity_sum_re_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_prod_dom
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_zero_psd
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_Nst_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_av_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_expand
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_gN_psd
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_len_le_cnt
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_mix_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_psd_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_ptSize_loc
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBA_p__prob_e1ba36bbace9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution : KB.TopOfLoc := by
  intro E _ _ _ Wp Wq _ _ _ _ S Λ' hpos _ hloc ε hε s hs2 hsr w _ hcnt
  have hcnt' : w.1.cnt + C.Kst ≤ S.Ntop := hcnt
  have hlen : ∀ v, (w.1 v).length + C.Kst ≤ S.Ntop := fun v =>
    le_trans (Nat.add_le_add_right (len_le_cnt S w.1 v) _) hcnt'
  choose U θ hUθ using fun v => hloc v s hs2 hsr (w.1 v) ⟨w, rfl⟩ (hlen v)
  have hU : ∀ v, ∀ a ∈ U v, D.AdmAt S v a ∧ a.length ≤ w.1.cnt + C.Kst := fun v a ha =>
    ⟨((hUθ v).1.2 a ha).1,
      le_trans ((hUθ v).1.2 a ha).2 (Nat.add_le_add_right (len_le_cnt S w.1 v) _)⟩
  have hw : w.1.cnt ≤ w.1.cnt + C.Kst := Nat.le_add_right _ _
  refine ⟨fun B => pθ S B w θ, fun B => pθ_prob (fun v _ => (hUθ v).1.1) (fun v _ => hU v) hw hcnt', ?_⟩
  intro Y hY κ hκ t ht B
  let g : Fin S.f → TB.Pt E → C.LPt := fun v h => C.loc (S.σ v) h ++ [(s, S.σ v t)]
  let G : Fin S.f → TB.Pt E → TB.Pt E → ℂ := fun v h h' =>
    KB.gN S v ε (S.G.r + 1) (w.1 v) (g v h) (g v h')
  let M : Fin S.f → TB.Pt E → TB.Pt E → ℂ := fun v h h' =>
    KB.mix S v ε (S.G.r + 1) (U v) (θ v) (g v h) (g v h')
  let c : Fin S.f → ℝ := fun v => (‖S.σ v t‖ * Λ' (S.G.r + 2 - s) s v) ^ (2 * C.Kst)
  let A : Fin S.f → TB.Pt E → TB.Pt E → ℂ := fun v h h' =>
    if v ∈ B then (c v : ℂ) * M v h h' else G v h h'
  have hG : ∀ v ∈ (univ : Finset (Fin S.f)), TB.PSDOn Y (G v) := fun v _ =>
    psd_comp _ _ (gN_psd S hpos v hε le_rfl w (Y.image (g v))) Y (g v)
      (fun h hh => mem_image_of_mem _ hh)
  have hAG : ∀ v ∈ (univ : Finset (Fin S.f)), TB.PSDOn Y (fun x y => A v x y - G v x y) := by
    intro v _
    by_cases hv : v ∈ B
    · have hσ : S.σ v t ≠ 0 := (map_ne_zero (S.σ v)).mpr ht
      have hY' : ∀ p ∈ Y.image (C.loc (S.σ v)), D.ptSize p = S.G.r + 1 - s := by
        intro p hp
        obtain ⟨h, hh, rfl⟩ := mem_image.mp hp
        rw [ptSize_loc]
        exact hY h hh
      have h1 := psd_comp _ _ ((hUθ v).2 ε hε (S.σ v t) _ hσ hY') Y (C.loc (S.σ v))
        (fun h hh => mem_image_of_mem _ hh)
      refine Jx8.psd_congr ?_ h1
      intro x _ y _
      simp only [A, if_pos hv]
      rfl
    · refine Jx8.psd_congr ?_ (Jx8.zero_psd Y)
      intro x _ y _
      simp only [A, if_neg hv, sub_self]
  have hle := BaseGramNonnegativity.sum_re_nonneg Y κ _ hκ (Jx7.psd_prod_dom univ G A hG hAG)
  have hprod : ∀ h h', ∏ v, A v h h' =
      (∏ v ∈ B, (c v : ℂ)) * ∏ v, (if v ∈ B then M v h h' else G v h h') := by
    intro h h'
    calc ∏ v, A v h h'
        = ∏ v, ((if v ∈ B then (c v : ℂ) else 1) * (if v ∈ B then M v h h' else G v h h')) :=
          prod_congr rfl (fun v _ => by by_cases hv : v ∈ B <;> simp [A, hv])
      _ = (∏ v, (if v ∈ B then (c v : ℂ) else 1)) * ∏ v, (if v ∈ B then M v h h' else G v h h') :=
          prod_mul_distrib
      _ = _ := by rw [prod_ite_mem, univ_inter]
  have hexp : ∀ h h', ∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst), (pθ S B w θ w' : ℂ) *
        ∏ v, KB.gN S v ε (S.G.r + 1) (w'.1 v) (g v h) (g v h') =
      ∏ v, (if v ∈ B then M v h h' else G v h h') := fun h h' =>
    expand (fun v _ => (hUθ v).1.1) (fun v _ => hU v) hw hcnt'
      (fun v a => KB.gN S v ε (S.G.r + 1) a (g v h) (g v h'))
  have hR : ∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst), (pθ S B w θ w' : ℂ) *
        S.base.Nst ε (S.G.r + 1) s w' Y κ t t =
      ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, (if v ∈ B then M v h h' else G v h h') := by
    simp only [Nst_eq S (i := S.G.r + 1) le_rfl]
    have hm := mix_sum Y (S.base.Wb (w.1.cnt + C.Kst)) κ 1 (fun w' => (pθ S B w θ w' : ℂ))
      (fun w' h h' => ∏ v, KB.gN S v ε (S.G.r + 1) (w'.1 v) (g v h) (g v h'))
    simp only [one_mul] at hm
    rw [← hm]
    refine sum_congr rfl fun h _ => sum_congr rfl fun h' _ => ?_
    rw [hexp h h']
  have hC : ∏ v ∈ B, (S.base.av v t * Λ' (S.G.r + 2 - s) s v) ^ (2 * S.base.K) = ∏ v ∈ B, c v :=
    prod_congr rfl fun v _ => by rw [av_eq]; rfl
  have hsum : ∑ w' ∈ S.base.Wb (S.base.cnt w + S.base.K),
        pθ S B w θ w' * (S.base.Nst ε (S.G.r + 1) s w' Y κ t t).re =
      (∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst), (pθ S B w θ w' : ℂ) *
        S.base.Nst ε (S.G.r + 1) s w' Y κ t t).re := by
    rw [Complex.re_sum]
    refine sum_congr rfl fun w' _ => ?_
    rw [Complex.re_ofReal_mul]
  rw [hC, hsum, hR, Nst_eq S (i := S.G.r + 1) le_rfl s w Y κ t t, ← Complex.re_ofReal_mul,
    Complex.ofReal_prod]
  have hA : (∏ v ∈ B, (c v : ℂ)) * ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, (if v ∈ B then M v h h' else G v h h') =
      ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, A v h h' := by
    rw [mul_sum]
    refine sum_congr rfl fun h _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun h' _ => ?_
    rw [hprod h h', mul_left_comm]
  rw [hA]
  simp only [mul_sub, sum_sub_distrib, Complex.sub_re] at hle
  linarith
end Formalism.FourierDecayAlt.P.PBA
