-- Prove2me | solution 1 for BCFGJPSSV26.Stable.Hyp.card_clusterWitness
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:18:31.739338+00:00
-- url     : https://prove2.me/submissions/4702d619-7bb1-426f-b416-7c901228076f

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSampling
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingDensity
public import Definitions.Def_BCFGJPSSV26_Stable_Structure_ClusterWitness
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingAnalysis
import all Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingAnalysis
public import Theorems.Thm_BCFGJPSSV26_Stable_Hyp_card_S_sdiff_LSX_le
public import Theorems.Thm_BCFGJPSSV26_Stable_KSData_card_good
public import Theorems.Thm_BCFGJPSSV26_Stable_KSData_inv_step
public import Theorems.Thm_BCFGJPSSV26_Stable_guided_count
public import Theorems.Thm_BCFGJPSSV26_Stable_ksRun_phase

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace KSData

variable (K : KSData)

/-- **The outcome at the end**: the invariant in phase `2` is a good outcome. -/
theorem witness {st : KSState} (hI : K.Inv st) (h2 : st.phase = 2) :
    Nonempty (ClusterWitness K.w₁ (K.X.I.centers (ksLS' K.LS st)) (toDums K.X.I st.dums)) := by
  obtain ⟨hcc1, htag⟩ := hI.ph2 h2
  have hcc0 : K.cc 0 st.del st.dums := hI.ph1 (by omega)
  have hb : K.Base st.del st.dums := hI.base
  have hg : K.GamSub st.del st.dums := hI.gam (by omega)
  have hlead : ∀ d ∈ st.dums, ∃ i ∈ st.del, d.1 = K.X.I.n + i := fun d hd ↦
    (hI.leaders d hd).resolve_right fun h ↦ by omega
  have hD : (toRaw K.X.I).ValidDums st.dums := fun d hd ↦ by
    obtain ⟨i, hi, he⟩ := hlead d hd
    have := (hb.del_sub i hi).1
    rw [he, Raw.n_toRaw, Raw.m_toRaw]
    omega
  have hLS' : K.X.I.centers (ksLS' K.LS st) = K.LSp st.del := rfl
  rw [hLS']
  unfold cc GoodL wt at hcc0 hcc1
  simp only [one_ne_zero, ↓reduceIte] at hcc0 hcc1
  refine ⟨{
    OL2 := K.matched st.dums
    φ := K.phi st.dums
    LS'_sub := K.LSp_subset _
    LSX_sub := hb.LSX_subset
    card_del := (card_le_card (sdiff_subset_sdiff subset_rfl hb.LSX_subset)).trans
      (K.H.card_S_sdiff_LSX_le K.w₁)
    OL2_sub := K.matched_subset _
    length_eq := by rw [K.length_toDums hD, hb.card]
    φ_mem := fun c hc ↦ K.phi_mem hD hc
    φ_inj := K.phi_injOn hb.dums_nodup
    leader := fun c hc ↦ by
      obtain ⟨i, hi, he⟩ := K.dumOf_cand hc
      refine ⟨i, (K.mem_GamE.1 hi).1, ?_⟩
      unfold phi
      rw [K.toDum_leader i.2 he]
    radius_ge := fun c hc ↦ (hb.rad c hc).1
    radius_le := fun c hc ↦ (hb.rad c hc).2
    Gam_sub := fun c hc ↦ by
      obtain ⟨c', -, hc'⟩ := mem_biUnion.1 hc
      exact K.mem_LSp.2 ⟨K.X.Gam_subset_S c' hc', hg c hc⟩
    cost₀ := hcc0
    cost₁ := hcc1 }⟩

end KSData

open Classical in
/-- **The process lemma of the cluster sampling.** -/
theorem Hyp.card_clusterWitness {X : Ctx} (H : Hyp X) {LS : List ℕ}
    (hLS : X.I.centers LS = X.S) (hLSnd : LS.Nodup) (hLSm : ∀ i ∈ LS, i < X.I.m)
    {Λ₁ : List DumQ} (hΛ₁ : (toRaw X.I).ValidDums Λ₁) (w₁ : ClientWitness X (toDums X.I Λ₁)) :
    X.P.q₂ ^ Par.M₂ X.P.N X.L * ((2 : ℝ) ^ X.b) ^ Par.M₂ X.P.N X.L ≤
      (univ.filter fun u : Fin (Par.M₂ X.P.N X.L) → Fin (2 ^ X.b) ↦
        Nonempty (ClusterWitness w₁
          (X.I.centers (ksLS' LS (ksRun X.P.N (toRaw X.I) LS Λ₁ X.s X.b (toCh u))))
          (toDums X.I (ksRun X.P.N (toRaw X.I) LS Λ₁ X.s X.b (toCh u)).dums))).card := by
  let K : KSData := ⟨X, H, LS, hLS, hLSnd, hLSm, Λ₁, hΛ₁, w₁⟩
  have hg := guided_count (fun _ st (v : Fin (2 ^ X.b)) ↦ K.step st v) ksInit
    (fun _ st ↦ K.Inv st) (fun _ st v ↦ K.Good st v) K.q₂_nonneg (Par.M₂ X.P.N X.L) K.inv_init
    (fun _ _ _ _ hI hG ↦ K.inv_step hI hG) (fun _ _ _ hI ↦ K.card_good hI)
  rw [K.card_fin_b] at hg
  refine hg.trans (Nat.cast_le.2 (card_le_card fun u hu ↦ ?_))
  rw [mem_filter] at hu ⊢
  refine ⟨mem_univ _, ?_⟩
  have hrun : ksRun X.P.N (toRaw X.I) LS Λ₁ X.s X.b (toCh u) =
      runFin (fun _ st (v : Fin (2 ^ X.b)) ↦ K.step st v) ksInit (Par.M₂ X.P.N X.L) u :=
    KSData.foldl_range_eq_runFin (fun st t ↦ K.step st t) ksInit (toCh u) _ u
      fun i h ↦ by unfold toCh; rw [dif_pos h]
  have h2 := ksRun_phase X.P.N (toRaw X.I) LS Λ₁ X.s X.b (toCh u)
  rw [hrun] at h2 ⊢
  exact K.witness hu.2 h2

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.Hyp.card_clusterWitness := @BCFGJPSSV26.Stable.Hyp.card_clusterWitness
