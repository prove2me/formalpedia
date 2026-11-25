-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.cover_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:56:02.647938+00:00
-- url     : https://prove2.me/submissions/0fb9b5fd-1b07-4905-bfe0-cd71d5b78ba7

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticGroupT2Space
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpE_eventually_det_pos
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpE_tendsto_sec
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpE_isInducing_F
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpE_metaplectic_group_t2Space
import Theorems.Thm_CompanionTheory_ThKR_LL_Intw_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_Iso_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_mul
import Theorems.Thm_CompanionTheory_ThKR_Mp_continuous_pr
import Theorems.Thm_CompanionTheory_ThKR_Mp_om_sch


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open MpE
namespace CompanionTheory.ThKR.Mp
theorem _root_.solution (hT : TopG l) (hO : Surj l) (hK : Ker l) (hS : SecEx l) (hD : SecDer l) : Cover l := by
  have : IsTopologicalGroup (G l) := hT
  have : T2Space (G l) := metaplectic_group_t2Space
  obtain ⟨ε, -, hker, -⟩ := hK
  have hσ : ∀ s : Sp l, ∃ g : G l, 0 < s.1.toBlocks₁₁.det → pr g = s ∧ omS g = sec s.1 := fun s => by
    by_cases h : 0 < s.1.toBlocks₁₁.det
    · obtain ⟨g, c, h1, h2, h3⟩ := hS s h.ne'
      exact ⟨g, fun _ => ⟨h1, by rw [h2, h3 h, one_smul]⟩⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose σ hσ using hσ
  have hd : DenseRange (schwartzToL2 l) := by
    have h := SchwartzMap.denseRange_toLpCLM (E := EuclideanSpace ℝ l) (F := ℂ)
      (μ := (volume : Measure (EuclideanSpace ℝ l))) (p := 2) ENNReal.ofNat_ne_top
    convert h using 1
    funext g
    rfl
  have hv : ∀ v : L2 l, Tendsto (fun s => om (σ s) v) (𝓝 1) (𝓝 v) := fun v => by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    obtain ⟨φ, hφ⟩ := hd.exists_dist_lt v (show 0 < δ / 3 by positivity)
    have h1 := (Metric.tendsto_nhds.1 (tendsto_sec hD φ)) (δ / 3) (by positivity)
    filter_upwards [h1, eventually_det_pos] with s hs1 hs2
    have e : om (σ s) (schwartzToL2 l φ) = schwartzToL2 l (sec s.1 φ) := by rw [om_sch, (hσ s hs2).2]
    calc dist (om (σ s) v) v ≤ dist (om (σ s) v) (om (σ s) (schwartzToL2 l φ)) +
          dist (om (σ s) (schwartzToL2 l φ)) (schwartzToL2 l φ) + dist (schwartzToL2 l φ) v := dist_triangle4 _ _ _ _
      _ < δ := by
        rw [(om (σ s)).isometry.dist_eq, e, dist_comm (schwartzToL2 l φ) v]
        linarith
  have key : Tendsto σ (𝓝 1) (𝓝 1) := by
    have hpr : Tendsto (fun s => pr (σ s)) (𝓝 (1 : Sp l)) (𝓝 1) :=
      tendsto_id.congr' (eventually_det_pos.mono fun s hs => (hσ s hs).1.symm)
    have h2 : Tendsto (fun s => ((pr (σ s), fun f => om (σ s) f) : Sp l × (L2 l → L2 l))) (𝓝 1)
        (𝓝 ((pr (1 : G l), fun f => om (1 : G l) f))) := by
      rw [map_one, map_one]
      refine hpr.prodMk_nhds (tendsto_pi_nhds.2 fun v => ?_)
      simpa using hv v
    exact isInducing_F.tendsto_nhds_iff.2 h2
  have hopen : IsOpenMap (pr : G l → Sp l) := by
    intro U hU
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨g, hg, rfl⟩
    have hc : Tendsto (fun t : Sp l => (pr g)⁻¹ * t) (𝓝 (pr g)) (𝓝 1) := by
      have : Continuous fun t : Sp l => (pr g)⁻¹ * t :=
        Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) fun t => ((pr g)⁻¹ * t).2
      simpa using this.tendsto (pr g)
    have h1 : Tendsto (fun t => g * σ ((pr g)⁻¹ * t)) (𝓝 (pr g)) (𝓝 g) := by
      have := ((continuous_const_mul g).tendsto 1).comp (key.comp hc)
      rwa [mul_one] at this
    filter_upwards [h1 (hU.mem_nhds hg), hc.eventually eventually_det_pos] with t ht ht'
    exact ⟨_, ht, by rw [map_mul, (hσ _ ht').1, mul_inv_cancel_left]⟩
  have hker' : ((pr : G l →* Sp l).ker : Set (G l)) = {1, ε} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hker g
  have hdisc : IsDiscrete ((pr : G l →* Sp l).ker : Set (G l)) := by
    rw [hker']
    exact ((Set.finite_singleton ε).insert 1).isDiscrete
  have hq : IsQuotientMap (pr : G l → Sp l) := hopen.isQuotientMap continuous_pr hO
  exact (hq.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom hdisc).isCoveringMap
end CompanionTheory.ThKR.Mp
