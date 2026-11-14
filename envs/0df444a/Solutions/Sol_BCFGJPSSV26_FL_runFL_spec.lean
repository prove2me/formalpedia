-- Prove2me | solution 1 for BCFGJPSSV26.FL.runFL_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:06:06.560624+00:00
-- url     : https://prove2.me/submissions/fafbf427-fdf6-4df5-95a2-9daeaa84cabb

module

public import Definitions.Def_BCFGJPSSV26_FL_Select
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Core
public import Definitions.Def_BCFGJPSSV26_FL_Run
import all Definitions.Def_BCFGJPSSV26_FL_Run
public import Theorems.Thm_BCFGJPSSV26_FL_fl_arith
public import Theorems.Thm_BCFGJPSSV26_FL_sol_eta
public import Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_complete_sol
public import Theorems.Thm_BCFGJPSSV26_Greedy_robust_lmp

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.FL

open Finset Greedy

variable {I : Instance}

/-- **The guarantee of the greedy run**: for `n ≥ 2`, `m ≥ 2`, `f > 0` and a nonempty set `O`
of positive cost, the run is a list of distinct facilities with
`cost S + λ f |S| ≤ λ (cost O + f |O|)`. -/
theorem runFL_spec (hI : I.Valid) (hn : 2 ≤ I.n) (hm : 2 ≤ I.m) {f : ℚ} (hf : 0 < f)
    {O : Finset (Fin I.m)} (hO : O.Nonempty) (hc : 0 < I.cost O) :
    I.IsCenterList (runFL (toRaw I) f) ∧
      (score (toRaw I) f (runFL (toRaw I) f) : ℝ) ≤ (lmpC : ℝ) * (I.cost O + f * O.card) := by
  obtain ⟨co, hco_def⟩ : ∃ co : ℚ, co = ∑ j, O.inf' hO fun i ↦ I.d (.inl j) (.inr i) :=
    ⟨_, rfl⟩
  have hco : (co : ℝ) = I.cost O := by rw [hco_def]; exact cast_costO hO
  have hco_pos : 0 < co := by exact_mod_cast (hco ▸ hc)
  obtain ⟨hdm_pos, hdm_le⟩ := dminFL_spec hI hO (hco_def ▸ hco_pos)
  rw [← hco_def] at hdm_le
  have hn0 : (0 : ℚ) < I.n := by exact_mod_cast (show 0 < I.n by omega)
  have hn1 : (1 : ℚ) ≤ I.n := by exact_mod_cast (show 1 ≤ I.n by omega)
  have ht : 0 < tFL (toRaw I) f := lt_min (div_pos hdm_pos (mul_pos (by norm_num [cS]) hn0)) hf
  have hX := hyp_ctxFL hI hn hm hf.le ht
  -- the opening cost
  have hfh0 := fhatFL_nonneg hf.le ht
  have hfh1 : lmpC * (1 - δ0) ≤ fhatFL (toRaw I) f := by
    unfold fhatFL
    rw [le_div_iff₀ ht]
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num [lmpC, δ0])
  have hnη : ((ctxFL (toRaw I) f).ip.n : ℚ) * (ctxFL (toRaw I) f).ip.η <
      fhatFL (toRaw I) f := by
    change ((toRaw I).n : ℚ) * ηFL (toRaw I).n < _
    have h1 := eta_bound (n := ((toRaw I).n : ℚ)) (s := 1) (δ := δ0) hn0 (by
      change (1 : ℚ) ≤ I.n
      exact_mod_cast (show 1 ≤ I.n by omega))
    rw [one_mul] at h1
    unfold ηFL
    have : δ0 ^ 2 / 100 < lmpC * (1 - δ0) := by norm_num [δ0, lmpC]
    linarith
  have hfM : fhatFL (toRaw I) f ≤ (ctxFL (toRaw I) f).ip.fmax := by
    change fhatFL (toRaw I) f ≤ 4 * ((toRaw I).n : ℚ) * MFL (toRaw I) f
    have hM : fhatFL (toRaw I) f ≤ MFL (toRaw I) f := by
      unfold MFL
      have : 0 ≤ (toRaw I).dMaxQ / tFL (toRaw I) f := by
        have := Instance.dMax_pos hI
        rw [← Raw.dMaxQ_toRaw] at this
        have : (0 : ℚ) < (toRaw I).dMaxQ := by exact_mod_cast this
        exact div_nonneg this.le ht.le
      linarith
    have : (1 : ℚ) ≤ 4 * ((toRaw I).n : ℚ) := by
      change (1 : ℚ) ≤ 4 * (I.n : ℚ)
      linarith
    nlinarith
  -- CompleteSolution gives a `0`-valid solution
  obtain ⟨hsol, hok⟩ := Ctx.complete_sol hX hnη hfM le_rfl (H := []) (by simp)
    (by simp [Ctx.SolOK]) (fun p hp ↦ by simp [Ctx.decH] at hp)
  set C := ctxFL (toRaw I) f with hC
  set H := C.complete (fhatFL (toRaw I) f) [] with hH
  have hreg : ∀ a ∈ H.flatten, a.2 = 0 := fun a ha ↦
    ((C.complete_atoms _ [] a ha).resolve_left (by simp)).1
  have hnr := Ctx.one_le_nRegA_of_sol hX hsol hreg
  obtain ⟨hne, hnd, hlt, hlen⟩ := Ctx.toCenters_spec hX hok hnr
  have hcost := Ctx.coreCost_toCenters_le hX hsol hok
  have hcore := coreCost_ctxFL (f := f) hne hlt ht
  -- the robust LMP guarantee with slack `0`
  set P' : Par := { C.par with η := 0 } with hP'
  have hP'g : P'.Good I.n := by
    have hg := hX.good
    refine ⟨hg.δ_pos, hg.δ_le, hg.ε_pos, hg.ε_le, le_rfl, ?_, hg.K_ge⟩
    change (I.n : ℚ) * 0 ≤ C.par.δ * C.par.ε / 10
    have := hg.δ_pos
    have := hg.ε_pos
    rw [mul_zero]
    positivity
  have hsol' : Sol P' (scSpace I hI _ ht).d (fhatFL (toRaw I) f) P'.η (Ctx.decH hX H) :=
    sol_eta hsol 0
  have hf' : (I.n : ℚ) * P'.η < fhatFL (toRaw I) f := by
    change (I.n : ℚ) * 0 < _
    rw [mul_zero]
    linarith [hfh1, show (0 : ℚ) < lmpC * (1 - δ0) by norm_num [lmpC, δ0]]
  have hlmp := robust_lmp (scSpace I hI _ ht) P' hP'g hX.d1 hf' hsol' O hO
  have hconn : connCost P' (scSpace I hI _ ht).d (Ctx.decH hX H) =
      connCost C.par (scSpace I hI _ ht).d (Ctx.decH hX H) := rfl
  rw [hconn, costF_scSpace hO, ← hco_def] at hlmp
  -- the number of facilities
  have hlenS : ((toCenters H).length : ℚ) ≤ (nReg (Ctx.decH hX H) : ℚ) := by
    have h1 : nRegA H = H.flatten.length := by
      unfold nRegA
      rw [List.filter_eq_self.2 fun a ha ↦ by simp [hreg a ha]]
    have h2 := Ctx.nRegA_eq hX H
    exact_mod_cast hlen.trans (h1.symm.trans h2).le
  have hnt : (I.n : ℚ) * tFL (toRaw I) f ≤ dminFL (toRaw I) / cS := by
    have h1 : tFL (toRaw I) f ≤ dminFL (toRaw I) / (cS * I.n) := min_le_left _ _
    have h2 := mul_le_mul_of_nonneg_left h1 hn0.le
    have e : (I.n : ℚ) * (dminFL (toRaw I) / (cS * I.n)) = dminFL (toRaw I) / cS := by
      field_simp
    linarith
  have hδP : P'.δ = δ0 := rfl
  rw [hδP] at hlmp
  have key := fl_arith ht hf.le rfl (hcore ▸ hcost) rfl hlenS hnt hdm_pos hdm_le hlmp
  refine ⟨⟨hne, hnd, hlt⟩, ?_⟩
  have hkey : ((score (toRaw I) f (toCenters H) : ℚ) : ℝ) ≤
      ((lmpC * (co + f * O.card) : ℚ) : ℝ) := by
    exact_mod_cast key
  rw [← hco]
  push_cast at hkey
  exact hkey

end BCFGJPSSV26.FL

end

public section

theorem solution : type_of% @BCFGJPSSV26.FL.runFL_spec := @BCFGJPSSV26.FL.runFL_spec
