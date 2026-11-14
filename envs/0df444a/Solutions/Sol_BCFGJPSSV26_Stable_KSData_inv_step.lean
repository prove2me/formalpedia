-- Prove2me | solution 1 for BCFGJPSSV26.Stable.KSData.inv_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:15:01.787115+00:00
-- url     : https://prove2.me/submissions/e9713bcc-2111-490f-bed5-f9028d6ad8b5

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingBridge
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingStep
import all Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingStep
public import Theorems.Thm_BCFGJPSSV26_Stable_KSData_Base_GoodL_eq_empty
public import Theorems.Thm_BCFGJPSSV26_Stable_KSData_Base_card_add_le
public import Theorems.Thm_BCFGJPSSV26_Stable_KSData_Base_card_del_le
public import Theorems.Thm_BCFGJPSSV26_Stable_KSData_Base_card_dums_le

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace KSData

variable (K : KSData)

/-- `START`: skip exactly when the cost condition holds; at the end of a phase, the condition
holds (if all of `S \ LS_X` is deleted, there is nothing left to pay). -/
theorem inv_tag0 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hI : K.Inv (ph, j, del, D, 0, l, r₀)) (hph : ph ≠ 2)
    (hG : K.Good (ph, j, del, D, 0, l, r₀) u) : K.Inv (K.step (ph, j, del, D, 0, l, r₀) u) := by
  have hph2 : ph < 2 := lt_of_le_of_ne hI.phase_le hph
  have hb : K.Base del D := hI.base
  have hg : K.GamSub del D := hI.gam (by simp)
  have hlead : ∀ d ∈ D, ∃ i ∈ del, d.1 = K.X.I.n + i := fun d hd ↦
    (hI.leaders d hd).resolve_right fun h ↦ absurd h.1 (by simp)
  have hs : K.cc ph del D ∨ j ≤ del.length := hI.start hph2 rfl
  have h1 : 1 ≤ ph → K.cc 0 del D := hI.ph1
  have hj : j ≤ K.X.s := hI.j_le
  rw [K.good_tag0 hph] at hG
  rw [K.step_tag0 hph]
  by_cases hjs : j = K.X.s
  · rw [if_pos hjs]
    have hcc : K.cc ph del D :=
      hs.elim id fun h ↦ K.cc_of_empty (hb.GoodL_eq_empty hg (by omega))
    by_cases h0 : ph = 0
    · rw [if_pos h0]
      subst h0
      exact Inv.mk_start K hb (by norm_num) (Nat.zero_le _) hlead hg (fun _ ↦ hcc)
        (.inr (Nat.zero_le _))
    · rw [if_neg h0]
      obtain rfl : ph = 1 := by omega
      exact Inv.mk_phase2 K hb hlead hg (h1 le_rfl) hcc
  · rw [if_neg hjs]
    have hG' := hG.resolve_left hjs
    by_cases hc : cbit K.X.b u = true
    · rw [if_pos hc]
      exact Inv.mk_start K hb hph2 (by omega) hlead hg h1 (.inl (hG'.1 hc))
    · rw [if_neg hc]
      have hns : ¬ K.cc ph del D := fun h ↦ hc (hG'.2 h)
      exact Inv.mk_sample K hb hph2 (by omega) hlead hg h1 (hs.resolve_left hns) hns

/-- `RADD`: delete the sampled center exactly when it is not a satellite of `O_B`; else it is a
satellite of some `c₀ ∈ O_B`, which has another kept satellite at distance in
`[ε per₀/2, 5 per₀)` (`BCFGJPSSV26.Stable.Hyp.no_dense_cores`). -/
theorem inv_tag2 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hI : K.Inv (ph, j, del, D, 2, l, r₀)) (hph : ph ≠ 2)
    (hG : K.Good (ph, j, del, D, 2, l, r₀) u) : K.Inv (K.step (ph, j, del, D, 2, l, r₀) u) := by
  have hph2 : ph < 2 := lt_of_le_of_ne hI.phase_le hph
  have hb : K.Base del D := hI.base
  have hg : K.GamSub del D := hI.gam (by simp)
  have hlead : ∀ d ∈ D, ∃ i ∈ del, d.1 = K.X.I.n + i := fun d hd ↦
    (hI.leaders d hd).resolve_right fun h ↦ absurd h.1 (by simp)
  have h1 : 1 ≤ ph → K.cc 0 del D := hI.ph1
  have hj : j < K.X.s := hI.j_lt (by simp)
  have hp : j ≤ del.length := hI.prog hph2 (by simp)
  obtain ⟨hlLS, hld, hgood⟩ := hI.radd hph2 rfl
  have hl : l < K.X.I.m := K.hm l hlLS
  rw [K.good_tag2 hph] at hG
  rw [K.step_tag2 hph]
  have hdel : del.length ≤ K.X.s := hb.card_del_le
  by_cases hc : cbit K.X.b u = true
  · rw [if_pos ⟨hdel, hc⟩]
    have hnot : K.fac l ∉ K.X.GamOf (K.OB D) := hG.1 hc
    have hS : K.fac l ∈ K.X.S \ K.X.LSX K.w₁.OL := by
      unfold GoodL at hgood
      split_ifs at hgood with h0
      · exact absurd hgood hnot
      · rcases mem_union.1 hgood with h | h
        · exact absurd h hnot
        · exact mem_sdiff.2 ⟨K.LSp_subset del (mem_sdiff.1 h).1, (mem_sdiff.1 h).2⟩
    refine Inv.mk_start K (hb.del_append hl hS hld) hph2 (by omega) ?_ ?_
      (fun h ↦ K.cc_zero_mono (h1 h) subset_rfl) (.inr (by simp; omega))
    · intro d hd
      obtain ⟨i, hi, he⟩ := hlead d hd
      exact ⟨i, List.mem_append_left _ hi, he⟩
    · intro c hc' hcd
      rcases List.mem_append.1 hcd with h | h
      · exact hg c hc' h
      · apply hnot
        rw [← List.mem_singleton.1 h, K.fac_fin]
        exact hc'
  · have hc' : ¬(del.length ≤ K.X.s ∧ cbit K.X.b u = true) := fun h ↦ hc h.2
    rw [if_neg hc']
    have hin : K.fac l ∈ K.X.GamOf (K.OB D) := by
      by_contra h
      exact hc (hG.2 h)
    obtain ⟨c₀, hc₀, hlc₀⟩ := mem_biUnion.1 hin
    obtain ⟨w, hw, hw1, hw2⟩ := K.exists_far_sat (K.isFar_of_OB hc₀) hlc₀
    refine Inv.mk_dg K hb hph2 hj hlead h1 hp ⟨hl, ?_, hld, ?_⟩
      ⟨c₀, hc₀, hlc₀, w, hw, hg w (mem_biUnion.2 ⟨c₀, hc₀, hw⟩), hw1, hw2⟩
    · exact mem_sdiff.2 ⟨K.X.Gam_subset_S c₀ hlc₀,
        K.not_mem_LSX_of_GamE (K.GamOf_OB_subset_GamE D hin)⟩
    · rintro c hc ⟨i, hi, hid⟩
      exact absurd hid (hg i (mem_biUnion.2 ⟨c, hc, hi⟩))

set_option maxHeartbeats 1000000 in
/-- `DG`: with `c'` the nearest other kept center, go to `RG` exactly when `ℓ` is a loose
satellite of some `c ∈ O_B` with `d(ℓ, c') ≥ ε² per`; then `r₀ = d(ℓ, c')` is comparable with the
percentiles (`BCFGJPSSV26.Stable.Hyp.comparable_per`). Else `d(ℓ, c') < ε² per₀`, so `c'` is a
loose satellite of `c₀`, outside `LS_X`, and every cluster losing the satellite `c'` can be led by
`ℓ` (`BCFGJPSSV26.Stable.Hyp.comparable_per` at `c'`). -/
theorem inv_tag3 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hI : K.Inv (ph, j, del, D, 3, l, r₀)) (hph : ph ≠ 2)
    (hG : K.Good (ph, j, del, D, 3, l, r₀) u) : K.Inv (K.step (ph, j, del, D, 3, l, r₀) u) := by
  have hph2 : ph < 2 := lt_of_le_of_ne hI.phase_le hph
  have hb : K.Base del D := hI.base
  have hlead : ∀ d ∈ D, ∃ i ∈ del, d.1 = K.X.I.n + i := fun d hd ↦
    (hI.leaders d hd).resolve_right fun h ↦ absurd h.1 (by simp)
  have h1 : 1 ≤ ph → K.cc 0 del D := hI.ph1
  have hj : j < K.X.s := hI.j_lt (by simp)
  have hp : j ≤ del.length := hI.prog hph2 (by simp)
  have hm : K.Mid del D l := hI.mid hph2 (by simp)
  have hdg : K.DGc del D l := hI.dg hph2 rfl
  obtain ⟨c₀, hc₀, hlc₀, w, hw, hwd, hw1, hw2⟩ := hdg
  have hfar₀ := K.isFar_of_OB hc₀
  have hp₀ := hfar₀.per_pos
  have he := K.H.eps_pos
  have he1 := K.H.eps_lt
  have hwl : w.1 ≠ l := by
    intro h
    have hw' : w = K.fac l := by rw [← h, K.fac_fin]
    rw [hw', Ctx.dF, Instance.dd_self K.H.valid] at hw1
    nlinarith
  obtain ⟨hc'lt, hc'S, hc'd, hc'l, hfd, hle⟩ :=
    K.nearOther_spec hm.lt (K.X.Gam_subset_S c₀ hw) hwd hwl
  rw [K.good_tag3 hph] at hG
  rw [K.step_tag3 hph]
  have hA := hb.card_add_le
  rw [if_neg (by omega)]
  have hne : K.LS.filter (fun c ↦ decide (c ∉ del ∧ c ≠ l)) ≠ [] :=
    List.ne_nil_of_mem (List.mem_filter.2 ⟨K.mem_S.1 (K.X.Gam_subset_S c₀ hw),
      decide_eq_true ⟨hwd, hwl⟩⟩)
  rw [if_neg hne]
  by_cases hc : cbit K.X.b u = true
  · rw [if_pos hc]
    obtain ⟨c₁, hc₁, hlc₁, hr₁⟩ := hG.1 hc
    have hfar₁ := K.isFar_of_OB hc₁
    refine Inv.mk_rg K hb hph2 hj (fun d hd ↦ .inl (hlead d hd)) h1 hp hm ⟨c₁, hc₁, hlc₁⟩
      ⟨?_, ?_⟩
    · have : 0 < K.X.ε ^ 2 * K.X.per c₁ := by have := hfar₁.per_pos; positivity
      linarith
    · intro c hc hlc
      have hfar := K.isFar_of_OB hc
      have hA1 := (K.H.comparable_per hfar hfar₁ ⟨K.fac l, mem_inter.2 ⟨hlc, hlc₁⟩⟩).1
      have hB2 := (K.H.comparable_per hfar hfar₀
        ⟨K.fac l, mem_inter.2 ⟨hlc, K.X.Gam_subset_GamE K.H.valid c₀ hlc₀⟩⟩).2
      have hpc := hfar.per_pos
      constructor
      · have : K.X.ε ^ 2 * K.X.per c / 3 ≤ K.X.ε ^ 2 * K.X.per c₁ := by
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hA1 (by positivity)
        linarith
      · rw [hfd]
        linarith
  · rw [if_neg hc]
    have hno : ¬∃ c ∈ K.OB D, K.fac l ∈ K.X.GamE c ∧
        K.X.ε ^ 2 * K.X.per c ≤ ((toRaw K.X.I).fdist (K.X.I.n + l) (K.nearOther del l) : ℝ) :=
      fun h ↦ hc (hG.2 h)
    have hlt : K.X.dF (K.fac l) (K.fac (K.nearOther del l)) < K.X.ε ^ 2 * K.X.per c₀ := by
      by_contra h
      push Not at h
      exact hno ⟨c₀, hc₀, K.X.Gam_subset_GamE K.H.valid c₀ hlc₀, by rw [hfd]; exact h⟩
    have hc'E : K.fac (K.nearOther del l) ∈ K.X.GamE c₀ := K.GamE_of_near hlc₀ hc'S hlt.le
    have hc'X : K.fac (K.nearOther del l) ∉ K.X.LSX K.w₁.OL :=
      K.not_mem_LSX_of_GamE (mem_biUnion.2 ⟨c₀, (K.mem_OB.1 hc₀).1, hc'E⟩)
    have hb' := hb.del_append hc'lt (mem_sdiff.2 ⟨hc'S, hc'X⟩) hc'd
    have hee : K.X.ε ^ 2 * K.X.per c₀ < K.X.ε * K.X.per c₀ / 2 := by
      have : K.X.ε ^ 2 < K.X.ε / 2 := by nlinarith
      nlinarith
    refine Inv.mk_dg K hb' hph2 hj ?_ (fun h ↦ K.cc_zero_mono (h1 h) subset_rfl)
      (by simp; omega) ⟨hm.lt, hm.mem, ?_, ?_⟩ ⟨c₀, hc₀, hlc₀, w, hw, ?_, hw1, hw2⟩
    · intro d hd
      obtain ⟨i, hi, he⟩ := hlead d hd
      exact ⟨i, List.mem_append_left _ hi, he⟩
    · rw [List.mem_append, List.mem_singleton, not_or]
      exact ⟨hm.nmem, fun h ↦ hc'l h.symm⟩
    · rintro c hc ⟨i, hi, hid⟩
      rcases List.mem_append.1 hid with h | h
      · exact hm.lose c hc ⟨i, hi, h⟩
      · have hi' : i = K.fac (K.nearOther del l) := by
          rw [← List.mem_singleton.1 h, K.fac_fin]
        rw [hi'] at hi
        have hfar := K.isFar_of_OB hc
        have hB2 := (K.H.comparable_per hfar hfar₀
          ⟨_, mem_inter.2 ⟨K.X.Gam_subset_GamE K.H.valid c hi, hc'E⟩⟩).2
        refine K.GamE_of_near' hi (mem_sdiff.1 hm.mem).1 ?_
        have : K.X.ε ^ 2 * K.X.per c₀ ≤ K.X.ε ^ 2 * (3 * K.X.per c) :=
          mul_le_mul_of_nonneg_left hB2 (by positivity)
        linarith
    · rw [List.mem_append, List.mem_singleton, not_or]
      refine ⟨hwd, fun h ↦ ?_⟩
      have hw' : w = K.fac (K.nearOther del l) := by rw [← h, K.fac_fin]
      rw [hw'] at hw1
      linarith

/-- `RG`: the radius is a grid point in `[d, (1 + ε) d]`, `d = d(c*, ℓ)` for the least
unmatched `c*` led by `ℓ`, shifted by less than `ε⁴ r₀ ≤ 15 ε⁴ per`; the new dummy is matched to
`c*`, and differs from the previous ones of the same leader. -/
theorem inv_tag4 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hI : K.Inv (ph, j, del, D, 4, l, r₀)) (hph : ph ≠ 2)
    (hG : K.Good (ph, j, del, D, 4, l, r₀) u) : K.Inv (K.step (ph, j, del, D, 4, l, r₀) u) := by
  have hph2 : ph < 2 := lt_of_le_of_ne hI.phase_le hph
  have hb : K.Base del D := hI.base
  have h1 : 1 ≤ ph → K.cc 0 del D := hI.ph1
  have hj : j < K.X.s := hI.j_lt (by simp)
  have hp : j ≤ del.length := hI.prog hph2 (by simp)
  have hm : K.Mid del D l := hI.mid hph2 (by simp)
  have hr : K.Rad0 D l r₀ := hI.rad0 hph2 (by simp)
  have hleadI : ∀ d ∈ D, (∃ i ∈ del, d.1 = K.X.I.n + i) ∨ (4 ≤ 4 ∧ d.1 = K.X.I.n + l ∧
      ∃ x < Par.Gr K.X.P.N, ∃ t < D.length, d.2 = ksRad K.X.P.N K.X.s r₀ x t) := hI.leaders
  have hrg : K.RGc D l := hI.rg hph2 rfl
  obtain ⟨c₂, hc₂, hlc₂⟩ := hrg
  rw [K.good_tag4 hph] at hG
  rw [K.step_tag4 hph]
  have hA := hb.card_add_le
  rw [if_neg (by omega)]
  have hcand₂ : K.Cand c₂ (K.X.I.n + l) := by
    have := K.cand_iff.2 hlc₂
    rwa [K.fac_val hm.lt] at this
  obtain ⟨c, hpick⟩ := K.pick_isSome (K.mem_OB.1 hc₂).1 (K.mem_OB.1 hc₂).2 hcand₂
  obtain ⟨hcO, hcM, hcand⟩ := K.pick_some hpick
  have hcOB : c ∈ K.OB D := K.mem_OB.2 ⟨hcO, hcM⟩
  have hlc : K.fac l ∈ K.X.GamE c := by
    rw [← K.fac_val hm.lt] at hcand
    exact K.cand_iff.1 hcand
  obtain ⟨hg1, hg2⟩ := hG c hpick
  have hr0 : 0 < r₀ := by exact_mod_cast hr.1
  have hDle : D.length ≤ 2 * K.X.s := by have := hb.card_dums_le; omega
  have hN1 : 1 ≤ K.X.P.N := by have := K.X.P.hN; omega
  set x := cunif (Par.Gr K.X.P.N) u with hx
  have hdD : (K.X.I.n + l, ksRad K.X.P.N K.X.s r₀ x D.length) ∉ D := by
    intro hd
    rcases hleadI _ hd with ⟨i, hi, he⟩ | ⟨-, -, x', -, t', ht', he⟩
    · have : l = i := by simp only at he; omega
      exact hm.nmem (this ▸ hi)
    · have := ksRad_inj hN1 hr0 hDle (by omega) he
      omega
  have heps : K.X.ε = 1 / (K.X.P.N : ℝ) := rfl
  have hd' : K.X.dF c (K.fac l) ≤ (1 + K.X.kap c + 3 * (1 / (K.X.P.N : ℝ))) * K.X.per c := by
    rw [K.dF_comm, ← heps]
    exact (K.mem_GamE.1 hlc).2.1
  have hbd := ksRad_bounds (s := K.X.s) (t := D.length) K.X.P.hN hr0.le hDle (K.per_nonneg' c)
    hg1 (by rw [← heps]; exact hg2) hd' (K.kap_le c) (hr.2 c hcOB hlc).2
  have hb' : K.Base del (D ++ [(K.X.I.n + l, ksRad K.X.P.N K.X.s r₀ x D.length)]) := by
    refine hb.dums_append hpick hdD ?_
    rw [K.toDum_leader (d := (K.X.I.n + l, _)) hm.lt rfl, K.toDum_radius, ← K.fac_eq hm.lt]
    exact ⟨hbd.1, by rw [heps]; exact hbd.2⟩
  refine Inv.mk_rgb K hb' hph2 hj ?_
    (fun h ↦ K.cc_zero_mono (h1 h) (K.OB_append_subset D _)) hp
    ⟨hm.lt, hm.mem, hm.nmem, fun c' hc' ↦ hm.lose c' (K.OB_append_subset D _ hc')⟩
    ⟨hr.1, fun c' hc' ↦ hr.2 c' (K.OB_append_subset D _ hc')⟩
  intro d hd
  rcases List.mem_append.1 hd with hd | hd
  · rcases hleadI d hd with h | ⟨-, h1', x', hx', t', ht', he⟩
    · exact .inl h
    · exact .inr ⟨h1', x', hx', t', by simp; omega, he⟩
  · rw [List.mem_singleton.1 hd]
    refine .inr ⟨rfl, x, Nat.mod_lt _ (by unfold Par.Gr; omega), D.length, by simp, rfl⟩

/-- **One step**: every good chunk keeps the invariant. -/
theorem inv_step {st : KSState} {u : ℕ} (hI : K.Inv st) (hG : K.Good st u) :
    K.Inv (K.step st u) := by
  obtain ⟨ph, j, del, D, tag, l, r₀⟩ := st
  by_cases hph : ph = 2
  · rw [show K.step (ph, j, del, D, tag, l, r₀) u = (ph, j, del, D, tag, l, r₀) from
      KSSteps.step_phase_two _ _ _ _ _ _ _ u hph]
    exact hI
  · have ht : tag ≤ 5 := hI.tag_le
    interval_cases tag
    · exact K.inv_tag0 hI hph hG
    · exact K.inv_tag1 hI hph hG
    · exact K.inv_tag2 hI hph hG
    · exact K.inv_tag3 hI hph hG
    · exact K.inv_tag4 hI hph hG
    · exact K.inv_tag5 hI hph hG

end KSData

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.KSData.inv_step := @BCFGJPSSV26.Stable.KSData.inv_step
