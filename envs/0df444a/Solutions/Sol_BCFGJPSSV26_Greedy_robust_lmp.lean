-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.robust_lmp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:04:53.086851+00:00
-- url     : https://prove2.me/submissions/58c0d289-1b2a-4cb1-add5-537dc1bb7544

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Embed
public import Definitions.Def_BCFGJPSSV26_Greedy_LMP
import all Definitions.Def_BCFGJPSSV26_Greedy_LMP
public import Theorems.Thm_BCFGJPSSV26_Greedy_FRP_boundOn
public import Theorems.Thm_BCFGJPSSV26_Greedy_Run_Zv_ge_third
public import Theorems.Thm_BCFGJPSSV26_Greedy_Run_embed_feasible
public import Theorems.Thm_BCFGJPSSV26_Greedy_Run_rstar_nonneg

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

namespace Run

variable {n m : ℕ} (R : Run n m)

/-- **[BCFGJPSSV26a, Lemma E.12]**, for one client: `Cost j ≤ term r⋆ j + 6 δ d(j, i⋆)`.
Without **FREEZING**, `r⋆ = r` and this is the chain lemma along the clients after `j`. With
**FREEZING**, the chain is cut at the step of `kl`, whose term is bounded in the two cases
`d(j, i₀⋆) ≤ θ / 3` (by [BCFGJPSSV26a, Lemma E.11]) and `d(j, i₀⋆) > θ / 3` (by the freezing
lemma). -/
theorem cost_le_term {Dg : Finset (Fin n)} (hne : Dg.Nonempty) {istar : Fin m}
    (hD : ∀ j ∈ Dg, ρ * R.X.d j istar ≤ R.αs j) (j : R.DgT Dg) :
    R.Cost j.val ≤ FRP.term (R.rstar hne istar) j + 6 * R.P.δ * R.X.d j.val istar := by
  have hd := R.X.d_nonneg j.val istar
  have hδ := R.good.δ_pos
  have h6 : 0 ≤ 6 * R.P.δ * R.X.d j.val istar := by positivity
  have hcontrib : ∀ s ∈ Ico (R.σ j.val) R.len,
      R.contrib j.val s ≤ bid (R.Xv j.val s) (R.Xv j.val (s + 1)) := fun s hs ↦ by
    rw [mem_Ico] at hs
    exact (R.contrib_le hs.1 hs.2).trans (bid_mono_left (R.Zv_le_Xv hs.1 hs.2) _)
  have hx : ∀ s, R.σ j.val ≤ s → s < R.len → R.Xv j.val (s + 1) ≤ R.Xv j.val s :=
    fun s h1 h2 ↦ R.Xv_anti h1 h2
  unfold FRP.term Cost
  by_cases hF : R.Freezing hne istar
  swap
  · -- no **FREEZING**: `r⋆ = r`
    simp only [R.rstar_of_not_freezing hne hF, r_eq]
    have hchain := Embed.chain_nxt (R.Xv j.val) R.time R.time_mono ⊤ (a := R.σ j.val)
      (fun s h1 h2 ↦ hx s h1 (by rwa [time_top] at h2)) (by rw [time_top]; exact R.Xv_nonneg _ _)
      j (by rw [time_coe]) le_top
    rw [time_coe, time_top] at hchain
    have hfil : univ.filter (fun k : R.DgT Dg ↦ j ≤ k ∧ (k : WithTop (R.DgT Dg)) < ⊤) =
        univ.filter (j ≤ ·) := filter_congr fun k _ ↦ by simp
    rw [hfil] at hchain
    have h1 := sum_le_sum hcontrib
    rw [time_top]
    linarith
  obtain ⟨a, hop, hgt, -, hc⟩ := id hF
  have hθl : R.θl hne = R.θs (R.σ (R.kl hne).val) := rfl
  have hs := R.σ_lt (R.kl hne).val
  have hjs := R.σ_le_σkl hne j
  have hkl := R.le_kl hne j
  -- the cost, cut at the step of `kl`
  have hsplit : ∑ s ∈ Ico (R.σ j.val) R.len, R.contrib j.val s =
      ∑ s ∈ Ico (R.σ j.val) (R.σ (R.kl hne).val), R.contrib j.val s +
        R.contrib j.val (R.σ (R.kl hne).val) +
        ∑ s ∈ Ico (R.σ (R.kl hne).val + 1) R.len, R.contrib j.val s := by
    rw [← sum_Ico_consecutive _ hjs hs.le, sum_eq_sum_Ico_succ_bot hs]
    ring
  have hA : ∑ s ∈ Ico (R.σ j.val) (R.σ (R.kl hne).val), R.contrib j.val s ≤
      ∑ s ∈ Ico (R.σ j.val) (R.σ (R.kl hne).val), bid (R.Xv j.val s) (R.Xv j.val (s + 1)) :=
    sum_le_sum fun s hs' ↦ hcontrib s (Ico_subset_Ico_right hs.le hs')
  have hchain := Embed.chain_nxt (R.Xv j.val) R.time R.time_mono (R.kl hne) (a := R.σ j.val)
    (fun s h1 h2 ↦ hx s h1 (by rw [time_coe] at h2; exact h2.trans hs))
    (by rw [time_coe]; exact R.Xv_nonneg _ _) j (by rw [time_coe]) (WithTop.coe_le_coe.2 hkl)
  rw [time_coe, time_coe] at hchain
  have hB := R.contrib_le hjs hs
  have hC : ∑ s ∈ Ico (R.σ (R.kl hne).val + 1) R.len, R.contrib j.val s + R.Xv j.val R.len ≤
      R.Xv j.val (R.σ (R.kl hne).val + 1) := by
    have h1 := sum_le_sum fun s (hs' : s ∈ Ico (R.σ (R.kl hne).val + 1) R.len) ↦
      hcontrib s (Ico_subset_Ico_left (by omega) hs')
    have h2 := bid_chain (show R.σ (R.kl hne).val + 1 ≤ R.len by omega)
      (fun s h1 h2 ↦ hx s (by omega) h2) (R.Xv_nonneg j.val R.len)
    linarith
  -- before `kf`, `r⋆ = r`; from `kf` on, the chain is constant
  have hcmp : ∑ k ∈ univ.filter (fun k : R.DgT Dg ↦ j ≤ k ∧
        (k : WithTop (R.DgT Dg)) < (R.kl hne : WithTop (R.DgT Dg))),
        bid (R.Xv j.val (R.time (k : WithTop (R.DgT Dg)))) (R.Xv j.val (R.time (FRP.nxt k))) ≤
      ∑ k ∈ univ.filter (fun k : R.DgT Dg ↦ j ≤ k ∧
        (k : WithTop (R.DgT Dg)) < (R.kl hne : WithTop (R.DgT Dg))),
        bid (R.rstar hne istar j k) (R.rstar hne istar j (FRP.nxt k)) := by
    refine sum_le_sum fun k hk ↦ ?_
    have hkkl := (mem_filter.1 hk).2.2
    by_cases hkf : R.kf hne ≤ k
    · have hσk := (R.of_kf_le hne hgt hkf).1
      have ht1 : R.time (FRP.nxt k) ≤ R.σ (R.kl hne).val :=
        R.time_mono (Embed.nxt_le_iff.2 hkkl)
      have ht2 : R.σ k.val ≤ R.time (FRP.nxt k) := R.time_mono (Embed.coe_lt_nxt k).le
      have ht : R.time (FRP.nxt k) = R.σ (R.kl hne).val := by omega
      rw [time_coe, ht, hσk, bid_self (R.Xv_nonneg j.val (R.σ (R.kl hne).val))]
      exact bid_nonneg _ _
    · rw [R.rstar_coe_of_not hne (fun h' ↦ hkf (WithTop.coe_le_coe.1 h'.2)), r_eq]
      exact bid_anti_right _ (by rw [← r_eq]; exact R.rstar_le_r hne j _)
  -- the step of `kl`
  have hlast : bid (R.Zv j.val (R.σ (R.kl hne).val)) (R.Xv j.val (R.σ (R.kl hne).val + 1)) +
      R.Xv j.val (R.σ (R.kl hne).val + 1) ≤
      R.rstar hne istar j (R.kl hne) + 6 * R.P.δ * R.X.d j.val istar := by
    have hZnear := R.Zv_ge_third hne hF j
    rw [R.rstar_of_kf_le hne hF (R.le_kl hne _)]
    rw [R.opened_eq hop] at hZnear ⊢
    have hY0 : 0 ≤ R.Xv j.val (R.σ (R.kl hne).val + 1) := R.Xv_nonneg _ _
    have hZX := R.Zv_le_Xv hjs hs
    have hYX := R.Xv_anti hjs hs
    -- `i₀⋆` is open after the step
    have hYd : R.Xv j.val (R.σ (R.kl hne).val + 1) ≤ R.X.d j.val a.fac := by
      rw [R.emb_Xv_of_lt (by omega : R.σ j.val < R.σ (R.kl hne).val + 1)]
      have hmem : a ∈ R.pre (R.σ (R.kl hne).val + 1) := by
        rw [R.pre_succ hs, hop.1]
        simp [Kind.atom?]
      have hoff : a.off = 0 := (R.sol.2.2.1 a (R.emb_mem_flatten hmem)).1 hop.2.2
      have hle : R.Dpre (R.σ (R.kl hne).val + 1) j.val ≤ R.X.d j.val a.fac + a.off :=
        profF_le R.P.K R.X.d (p := a.pair)
          (List.mem_toFinset.2 (List.mem_map_of_mem hmem)) j.val
      rw [hoff, add_zero] at hle
      have := R.X.d_nonneg j.val a.fac
      have := R.good.one_sub_δ_pos
      nlinarith
    have hθ := R.θl_pos hne
    split_ifs with hnear
    · have hZ := hZnear hnear
      have hYZ : R.Xv j.val (R.σ (R.kl hne).val + 1) ≤ R.Zv j.val (R.σ (R.kl hne).val) := by
        linarith
      have := bid_le_sub hYZ hY0
      linarith
    · push Not at hnear
      set Z := R.Zv j.val (R.σ (R.kl hne).val)
      set Y := R.Xv j.val (R.σ (R.kl hne).val + 1)
      set X := R.Xv j.val (R.σ (R.kl hne).val)
      by_cases hYW : Y ≤ min X (max Z (R.X.d j.val istar))
      · have h1 : bid Z Y ≤ bid (min X (max Z (R.X.d j.val istar))) Y :=
          bid_mono_left (le_min hZX (le_max_left _ _)) _
        have h2 := bid_le_sub hYW hY0
        linarith
      · push Not at hYW
        have hW : min X (max Z (R.X.d j.val istar)) = max Z (R.X.d j.val istar) := by
          rcases min_choice X (max Z (R.X.d j.val istar)) with h | h
          · rw [h] at hYW
            linarith
          · exact h
        rw [hW] at hYW ⊢
        have h0 : bid Z Y = 0 := bid_eq_zero_of_le ((le_max_left _ _).trans hYW.le) hY0
        have hfz := (R.freezing hD (k := (R.kl hne).val) (R.kl hne).2 hop hgt hc).1
        rw [← hθl] at hfz
        have htri := R.X.d_le_d_add_dF j.val a.fac istar
        have hδθ : R.P.δ * R.θl hne ≤ R.θl hne / 100 := by
          have := mul_le_mul_of_nonneg_right R.good.δ_le hθ.le
          linarith
        have hθ6 : R.θl hne ≤ 6 * R.X.d j.val istar := by linarith
        have := mul_le_mul_of_nonneg_left hθ6 hδ.le
        have := le_max_right Z (R.X.d j.val istar)
        linarith
  -- the term of `j`
  have hfil : univ.filter (fun k : R.DgT Dg ↦ j ≤ k) = insert (R.kl hne)
      (univ.filter (fun k : R.DgT Dg ↦ j ≤ k ∧
        (k : WithTop (R.DgT Dg)) < (R.kl hne : WithTop (R.DgT Dg)))) := by
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_insert, WithTop.coe_lt_coe]
    constructor
    · intro h
      rcases (R.le_kl hne k).lt_or_eq with h' | h'
      · exact .inr ⟨h, h'⟩
      · exact .inl h'
    · rintro (rfl | ⟨h, _⟩)
      · exact hkl
      · exact h
  have hnot : R.kl hne ∉ univ.filter (fun k : R.DgT Dg ↦ j ≤ k ∧
      (k : WithTop (R.DgT Dg)) < (R.kl hne : WithTop (R.DgT Dg))) := by simp
  have hnxt : FRP.nxt (R.kl hne) = ⊤ := Embed.nxt_eq_top_of_max (R.le_kl hne)
  have hW0 : 0 ≤ R.rstar hne istar j (R.kl hne) := R.rstar_nonneg hne hD j _
  rw [hfil, sum_insert hnot, hnxt, R.rstar_top_of hne hF, bid_zero_right hW0, hsplit]
  linarith

/-- **[BCFGJPSSV26a, Lemma E.12]**. -/
theorem cost_le_frp {Dg : Finset (Fin n)} (hne : Dg.Nonempty) {istar : Fin m}
    (hD : ∀ j ∈ Dg, ρ * R.X.d j istar ≤ R.αs j) :
    ∑ j ∈ Dg, R.Cost j ≤
      ∑ j : R.DgT Dg, FRP.term (R.rstar hne istar) j + 6 * R.P.δ * ∑ j ∈ Dg, R.X.d j istar := by
  rw [← R.sum_DgT Dg R.Cost, ← R.sum_DgT Dg (fun j ↦ R.X.d j istar), mul_sum,
    ← sum_add_distrib]
  exact sum_le_sum fun j _ ↦ R.cost_le_term hne hD j

/-- **[BCFGJPSSV26a, Lemma E.17]**: the clients of `Dg` pay at most
`f + (ρ + 6δ) ∑_{Dg} d(j, i⋆)`. -/
theorem dgood_cost {Dg : Finset (Fin n)} (hne : Dg.Nonempty) {istar : Fin m}
    (hD : ∀ j ∈ Dg, ρ * R.X.d j istar ≤ R.αs j) :
    ∑ j ∈ Dg, R.Cost j ≤ R.f + (ρ + 6 * R.P.δ) * ∑ j ∈ Dg, R.X.d j istar := by
  have h1 := R.cost_le_frp hne hD
  have hpos : 0 < ∑ j : R.DgT Dg, R.X.d j.val istar := by
    rw [R.sum_DgT Dg (fun j ↦ R.X.d j istar)]
    exact sum_pos (fun j _ ↦ lt_of_lt_of_le one_pos (R.d1 j istar)) hne
  have h2 := FRP.boundOn (R.embed_feasible hne hD) hpos
  rw [R.sum_DgT Dg (fun j ↦ R.X.d j istar)] at h2
  linarith

/-- The clients nearest to `o ∈ O` pay at most `f + (ρ + 6δ) ∑ d(j, o)`. -/
theorem fiber_cost (Fo : Finset (Fin n)) (o : Fin m) :
    ∑ j ∈ Fo, R.Cost j ≤ R.f + (ρ + 6 * R.P.δ) * ∑ j ∈ Fo, R.X.d j o := by
  classical
  set Dg := Fo.filter fun j ↦ ρ * R.X.d j o ≤ R.αs j with hDg
  have hf : 0 ≤ R.f := by
    have := R.fpos
    have := R.good.η_nonneg
    have : (0 : ℚ) ≤ n * R.P.η := by positivity
    linarith
  have hδ := R.good.δ_pos
  have hsplit := sum_filter_add_sum_filter_not Fo (fun j ↦ ρ * R.X.d j o ≤ R.αs j) R.Cost
  have hsplit' := sum_filter_add_sum_filter_not Fo (fun j ↦ ρ * R.X.d j o ≤ R.αs j)
    fun j ↦ R.X.d j o
  have hgood : ∑ j ∈ Dg, R.Cost j ≤ R.f + (ρ + 6 * R.P.δ) * ∑ j ∈ Dg, R.X.d j o := by
    rcases Dg.eq_empty_or_nonempty with he | hne
    · rw [he, sum_empty, sum_empty, mul_zero, add_zero]
      exact hf
    · exact R.dgood_cost hne fun j hj ↦ (mem_filter.1 hj).2
  have hbad : ∑ j ∈ Fo.filter (fun j ↦ ¬ ρ * R.X.d j o ≤ R.αs j), R.Cost j ≤
      (ρ + 6 * R.P.δ) * ∑ j ∈ Fo.filter (fun j ↦ ¬ ρ * R.X.d j o ≤ R.αs j), R.X.d j o := by
    rw [mul_sum]
    refine sum_le_sum fun j hj ↦ ?_
    have h := (mem_filter.1 hj).2
    push Not at h
    have := R.cost_le_alpha j
    have := R.X.d_nonneg j o
    nlinarith
  rw [← hsplit, ← hsplit', mul_add]
  linarith

/-- **The robust LMP guarantee**, for a run and a nonempty set `O` of facilities. -/
theorem lmp (O : Finset (Fin m)) (hO : O.Nonempty) :
    (1 - R.P.δ) * connCost R.P R.X.d R.H + nReg R.H * R.f ≤
      (ρ + 6 * R.P.δ) * costF R.X.d O + O.card * R.f + nReg R.H * n * R.P.η := by
  classical
  -- a nearest facility of `O` for each client
  have hnear : ∀ j : Fin n, ∃ o ∈ O, R.X.d j o = O.inf' hO (R.X.d j) := fun j ↦ by
    obtain ⟨o, ho, h⟩ := O.exists_mem_eq_inf' hO (R.X.d j)
    exact ⟨o, ho, h.symm⟩
  choose near hnearO hneard using hnear
  have hfib : ∑ j, R.Cost j = ∑ o ∈ O, ∑ j ∈ univ.filter (fun j ↦ near j = o), R.Cost j :=
    (sum_fiberwise_of_maps_to (fun j _ ↦ hnearO j) _).symm
  have hcost : costF R.X.d O =
      ∑ o ∈ O, ∑ j ∈ univ.filter (fun j ↦ near j = o), R.X.d j o := by
    unfold costF
    simp only [dif_pos hO]
    rw [← sum_fiberwise_of_maps_to (fun j _ ↦ hnearO j)]
    refine sum_congr rfl fun o _ ↦ sum_congr rfl fun j hj ↦ ?_
    rw [← (mem_filter.1 hj).2, hneard j]
  have hsum : ∑ j, R.Cost j ≤ O.card * R.f + (ρ + 6 * R.P.δ) * costF R.X.d O := by
    rw [hfib, hcost, mul_sum, ← nsmul_eq_mul, ← sum_const, ← sum_add_distrib]
    exact sum_le_sum fun o _ ↦ R.fiber_cost _ o
  have hsplit := R.cost_split
  nlinarith

end Run

/-- **The robust LMP guarantee** ([BCFGJPSSV26a, Theorem D.7], linear form). -/
theorem robust_lmp {n m : ℕ} (X : Space n m) (P : Par) (hP : P.Good n) (hd1 : ∀ j i, 1 ≤ X.d j i)
    {f : ℚ} (hf : n * P.η < f) {H : List (List (Atom m))} (hH : Sol P X.d f P.η H)
    (O : Finset (Fin m)) (hO : O.Nonempty) :
    (1 - P.δ) * connCost P X.d H + nReg H * f ≤
      (ρ + 6 * P.δ) * costF X.d O + O.card * f + nReg H * n * P.η :=
  Run.lmp ⟨X, P, f, H, hP, hd1, hf, hH⟩ O hO

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.robust_lmp := @BCFGJPSSV26.Greedy.robust_lmp
