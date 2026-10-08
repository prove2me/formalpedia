-- Prove2me | solution 1 for GPSAnalysis.Core.kkt_of_conforming
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T10:18:54.748239+00:00
-- url     : https://prove2.me/submissions/d31bdd27-4425-4498-9566-ab15e22067e2

import Mathlib
import Definitions.Def_GPSAnalysis_Core_Problem
import Definitions.Def_GPSAnalysis_Core_Mesh
import Definitions.Def_GPSAnalysis_Core_Run
import Definitions.Def_GPSAnalysis_Core_Clarke
import Definitions.Def_GPSAnalysis_Core_Cones

set_option autoImplicit false

namespace GPSAnalysis.Core

open Matrix

open Filter Topology in
theorem Sol_pv_b3a67880_Δpos {n m p : ℕ} {P : GPSSetup n m p}
    (R : GPSRun P) : ∀ k, 0 < R.Δ k := by
  intro k
  induction k with
  | zero => exact R.Δ_zero_pos
  | succ k ih =>
    rw [R.Δ_succ k]
    have hτ : (0 : ℝ) < (P.τ : ℝ) := by
      have := P.one_lt_τ
      have h1 : (1 : ℝ) < (P.τ : ℝ) := by exact_mod_cast this
      linarith
    exact mul_pos (zpow_pos hτ _) ih

theorem Sol_pv_b3a67880_xmem {n m p : ℕ} {P : GPSSetup n m p}
    (R : GPSRun P) (hA1 : AssumptionA1 R) : ∀ k, R.x k ∈ P.Ω := by
  intro k
  induction k with
  | zero =>
    by_contra hn
    have : P.fΩ (R.x 0) = ⊤ := by
      unfold GPSSetup.fΩ barrier
      rw [if_neg hn]
    unfold AssumptionA1 at hA1
    rw [this] at hA1
    exact lt_irrefl _ hA1
  | succ k ih =>
    by_cases h : R.meshLocalOpt k
    · rw [(R.localOpt k h).2.1]; exact ih
    · exact ((R.improved k h).1).2

theorem Sol_pv_b3a67880_closed {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (lo up : Fin m → EReal) :
    IsClosed (feasibleSet A lo up) := by
  have hcont : Continuous (fun v : Fin n → ℝ => A *ᵥ v) :=
    Continuous.matrix_mulVec continuous_const continuous_id
  have : feasibleSet A lo up = ⋂ r, ({v : Fin n → ℝ | lo r ≤ (((A *ᵥ v) r : ℝ) : EReal)} ∩
      {v : Fin n → ℝ | (((A *ᵥ v) r : ℝ) : EReal) ≤ up r}) := by
    ext v; simp [feasibleSet]
  rw [this]
  refine isClosed_iInter fun r => ?_
  have hc : Continuous (fun v : Fin n → ℝ => (((A *ᵥ v) r : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp ((continuous_apply r).comp hcont)
  exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)

open Filter in
theorem Sol_pv_b3a67880_pigeon {p : ℕ} {Q : Finset (Fin p) → ℕ → Prop}
    (h : ∀ᶠ i in atTop, ∃ S, Q S i) : ∃ S, ∃ᶠ i in atTop, Q S i := by
  by_contra hc
  push_neg at hc
  have h2 : ∀ᶠ i in atTop, ∀ S, ¬ Q S i := by
    rw [Filter.eventually_all]
    intro S
    exact hc S
  obtain ⟨i, ⟨S, hS⟩, hi⟩ := (h.and h2).exists
  exact hi S hS

open Filter Topology in
theorem Sol_pv_b3a67880_poly {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (lo up : Fin m → EReal)
    (xhat d : Fin n → ℝ) (hx : xhat ∈ feasibleSet A lo up)
    (hd : d ∈ tangentCone (feasibleSet A lo up) xhat)
    (xs : ℕ → Fin n → ℝ) (ts : ℕ → ℝ) (hxs : ∀ i, xs i ∈ feasibleSet A lo up)
    (hts : ∀ i, 0 ≤ ts i) (hlim : Tendsto xs atTop (𝓝 xhat)) (htl : Tendsto ts atTop (𝓝 0)) :
    ∀ᶠ i in atTop, xs i + ts i • d ∈ feasibleSet A lo up := by
  have hy : Tendsto (fun i => xs i + ts i • d) atTop (𝓝 xhat) := by
    simpa using hlim.add (htl.smul_const d)
  have hcont : Continuous (fun v : Fin n → ℝ => A *ᵥ v) :=
    Continuous.matrix_mulVec continuous_const continuous_id
  have hT : ∀ r, Tendsto (fun i => (((A *ᵥ (xs i + ts i • d)) r : ℝ) : EReal)) atTop
      (𝓝 (((A *ᵥ xhat) r : ℝ) : EReal)) := fun r =>
    (continuous_coe_real_ereal.tendsto _).comp
      ((((continuous_apply r).comp hcont).tendsto _).comp hy)
  have hsplit : ∀ i r, (A *ᵥ (xs i + ts i • d)) r = (A *ᵥ xs i) r + ts i * (A *ᵥ d) r := by
    intro i r
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    simp [smul_eq_mul]
  have hact_lo : ∀ r, lo r = (((A *ᵥ xhat) r : ℝ) : EReal) → 0 ≤ (A *ᵥ d) r := by
    intro r hr
    have hsub : {v | ∃ μ : ℝ, 0 ≤ μ ∧ ∃ w ∈ feasibleSet A lo up, v = μ • (w - xhat)} ⊆
        {v : Fin n → ℝ | 0 ≤ (A *ᵥ v) r} := by
      rintro v ⟨μ, hμ, w, hw, rfl⟩
      have h1 := (hw r).1
      rw [hr] at h1
      have h2 : (A *ᵥ xhat) r ≤ (A *ᵥ w) r := EReal.coe_le_coe_iff.mp h1
      show 0 ≤ (A *ᵥ (μ • (w - xhat))) r
      rw [Matrix.mulVec_smul, Matrix.mulVec_sub]
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      exact mul_nonneg hμ (by linarith)
    have hcl : IsClosed {v : Fin n → ℝ | 0 ≤ (A *ᵥ v) r} :=
      isClosed_le continuous_const ((continuous_apply r).comp hcont)
    exact closure_minimal hsub hcl hd
  have hact_up : ∀ r, up r = (((A *ᵥ xhat) r : ℝ) : EReal) → (A *ᵥ d) r ≤ 0 := by
    intro r hr
    have hsub : {v | ∃ μ : ℝ, 0 ≤ μ ∧ ∃ w ∈ feasibleSet A lo up, v = μ • (w - xhat)} ⊆
        {v : Fin n → ℝ | (A *ᵥ v) r ≤ 0} := by
      rintro v ⟨μ, hμ, w, hw, rfl⟩
      have h1 := (hw r).2
      rw [hr] at h1
      have h2 : (A *ᵥ w) r ≤ (A *ᵥ xhat) r := EReal.coe_le_coe_iff.mp h1
      show (A *ᵥ (μ • (w - xhat))) r ≤ 0
      rw [Matrix.mulVec_smul, Matrix.mulVec_sub]
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos hμ (by linarith)
    have hcl : IsClosed {v : Fin n → ℝ | (A *ᵥ v) r ≤ 0} :=
      isClosed_le ((continuous_apply r).comp hcont) continuous_const
    exact closure_minimal hsub hcl hd
  have hlo : ∀ r, ∀ᶠ i in atTop, lo r ≤ (((A *ᵥ (xs i + ts i • d)) r : ℝ) : EReal) := by
    intro r
    rcases ((hx r).1).eq_or_lt with h | h
    · refine Eventually.of_forall fun i => ?_
      have had := hact_lo r h
      rw [hsplit]
      calc lo r ≤ (((A *ᵥ xs i) r : ℝ) : EReal) := (hxs i r).1
        _ ≤ _ := EReal.coe_le_coe_iff.mpr (by nlinarith [hts i])
    · exact ((hT r).eventually (lt_mem_nhds h)).mono fun i hi => hi.le
  have hup : ∀ r, ∀ᶠ i in atTop, (((A *ᵥ (xs i + ts i • d)) r : ℝ) : EReal) ≤ up r := by
    intro r
    rcases ((hx r).2).eq_or_lt with h | h
    · refine Eventually.of_forall fun i => ?_
      have had := hact_up r h.symm
      rw [hsplit]
      calc (((A *ᵥ xs i) r + ts i * (A *ᵥ d) r : ℝ) : EReal) ≤ (((A *ᵥ xs i) r : ℝ) : EReal) :=
            EReal.coe_le_coe_iff.mpr (by nlinarith [hts i])
        _ ≤ up r := (hxs i r).2
    · exact ((hT r).eventually (gt_mem_nhds h)).mono fun i hi => hi.le
  filter_upwards [Filter.eventually_all.2 hlo, Filter.eventually_all.2 hup] with i h1 h2
  exact fun r => ⟨h1 r, h2 r⟩

open Filter Topology in
theorem Sol_pv_b3a67880_dir {n m p : ℕ} (P : GPSSetup n m p) (R : GPSRun P)
    (K : ℕ → ℕ) (hK : IsRefiningSubseq R K) (xhat : Fin n → ℝ)
    (hlim : Tendsto (fun i => R.x (K i)) atTop (𝓝 xhat))
    (U : Set (Fin n → ℝ)) (hU : U ∈ 𝓝 xhat) (g : (Fin n → ℝ) → ℝ)
    (hfg : ∀ y ∈ U, P.f y = (g y : WithTop ℝ))
    (grad : Fin n → ℝ) (hgrad : HasStrictDirGradAt g grad xhat) (j : Fin p)
    (hj : ∃ᶠ i in atTop, j ∈ R.Dk (K i))
    (hfeas : ∀ᶠ i in atTop, R.x (K i) + R.Δ (K i) • P.dir j ∈ P.Ω) :
    0 ≤ grad ⬝ᵥ direction P.D j := by
  have hpos := Sol_pv_b3a67880_Δpos R
  have hΔ : Tendsto (fun i => R.Δ (K i)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hK.2.2, Eventually.of_forall fun i => hpos (K i)⟩
  have hφ : Tendsto (fun i => (R.x (K i), R.Δ (K i))) atTop (𝓝 xhat ×ˢ 𝓝[>] (0 : ℝ)) :=
    hlim.prodMk hΔ
  have hpoll : Tendsto (fun i => R.x (K i) + R.Δ (K i) • P.dir j) atTop (𝓝 xhat) := by
    have := hlim.add (hK.2.2.smul_const (P.dir j))
    simpa using this
  have hevU : ∀ᶠ i in atTop, R.x (K i) ∈ U ∧ R.x (K i) + R.Δ (K i) • P.dir j ∈ U :=
    (hlim.eventually hU).and (hpoll.eventually hU)
  have hfreq : ∃ᶠ i in atTop, (0 : ℝ) ≤
      (g (R.x (K i) + R.Δ (K i) • P.dir j) - g (R.x (K i))) / R.Δ (K i) := by
    refine ((hj.and_eventually hfeas).and_eventually hevU).mono ?_
    rintro i ⟨⟨hjD, hΩ⟩, hxU, hpU⟩
    have hopt := ((R.localOpt (K i) (hK.2.1 i)).1 j hjD)
    have hfp : P.fΩ (R.x (K i) + R.Δ (K i) • P.dir j) =
        (g (R.x (K i) + R.Δ (K i) • P.dir j) : WithTop ℝ) := by
      unfold GPSSetup.fΩ barrier
      rw [if_pos hΩ, hfg _ hpU]
    rw [hfp] at hopt
    have hxΩ : R.x (K i) ∈ P.Ω := by
      by_contra hn
      have : P.fΩ (R.x (K i)) = ⊤ := by
        unfold GPSSetup.fΩ barrier
        rw [if_neg hn]
      rw [this] at hopt
      exact absurd hopt (by simp)
    have hfx : P.fΩ (R.x (K i)) = (g (R.x (K i)) : WithTop ℝ) := by
      unfold GPSSetup.fΩ barrier
      rw [if_pos hxΩ, hfg _ hxU]
    rw [hfx] at hopt
    have hle : g (R.x (K i)) ≤ g (R.x (K i) + R.Δ (K i) • P.dir j) := WithTop.coe_le_coe.mp hopt
    exact div_nonneg (by linarith) (hpos (K i)).le
  have hT : Tendsto (fun i => (g (R.x (K i) + R.Δ (K i) • P.dir j) - g (R.x (K i))) / R.Δ (K i))
      atTop (𝓝 (grad ⬝ᵥ P.dir j)) := (hgrad (P.dir j)).comp hφ
  by_contra h
  push_neg at h
  obtain ⟨i, hi1, hi2⟩ := (hfreq.and_eventually (hT.eventually (gt_mem_nhds h))).exists
  exact absurd hi1 (not_le.mpr hi2)

end GPSAnalysis.Core

open Filter Topology GPSAnalysis.Core in
theorem solution {n m p : ℕ} (P : GPSSetup n m p) (R : GPSRun P)
    (hA1 : AssumptionA1 R) (hA2 : AssumptionA2 P) (hA3 : AssumptionA3 R)
    (K : ℕ → ℕ) (hK : IsRefiningSubseq R K) (xhat : Fin n → ℝ)
    (hlim : Tendsto (fun i => R.x (K i)) atTop (𝓝 xhat))
    (U : Set (Fin n → ℝ)) (hU : U ∈ 𝓝 xhat) (g : (Fin n → ℝ) → ℝ)
    (hfg : ∀ y ∈ U, P.f y = (g y : WithTop ℝ)) (L : NNReal) (hL : LipschitzOnWith L g U)
    (grad : Fin n → ℝ) (hgrad : HasStrictDirGradAt g grad xhat)
    (ε : ℝ) (hε : 0 < ε) (hconf : ConformsTo R ε) :
    (∀ w ∈ tangentCone P.Ω xhat, 0 ≤ grad ⬝ᵥ w) ∧ -grad ∈ normalCone P.Ω xhat := by
  have hxΩ := Sol_pv_b3a67880_xmem R hA1
  have hpos := Sol_pv_b3a67880_Δpos R
  have hcl : IsClosed P.Ω := Sol_pv_b3a67880_closed P.A P.lo P.up
  have hxhat : xhat ∈ P.Ω := hcl.mem_of_tendsto hlim (Eventually.of_forall fun i => hxΩ (K i))
  have key : ∀ S : Finset (Fin p), (∃ᶠ i in atTop, S ⊆ R.Dk (K i)) →
      (∀ j ∈ S, ∀ᶠ i in atTop, R.x (K i) + R.Δ (K i) • P.dir j ∈ P.Ω) →
      ∀ w ∈ nonnegSpan P.D S, 0 ≤ grad ⬝ᵥ w := by
    rintro S hS hf w ⟨c, hc, rfl⟩
    rw [dotProduct_sum]
    refine Finset.sum_nonneg fun j hj => ?_
    rw [dotProduct_smul, smul_eq_mul]
    exact mul_nonneg (hc j) (Sol_pv_b3a67880_dir P R K hK xhat hlim U hU g hfg grad hgrad j
      (hS.mono fun i h => h hj) (hf j hj))
  have hfirst : ∀ w ∈ tangentCone P.Ω xhat, 0 ≤ grad ⬝ᵥ w := by
    by_cases hfr : xhat ∈ frontier P.Ω
    · have hev : ∀ᶠ i in atTop, ∃ S, S ⊆ R.Dk (K i) ∧
          tangentCone P.Ω xhat = nonnegSpan P.D S := by
        have := (Metric.tendsto_nhds.1 hlim) ε hε
        filter_upwards [this] with i hi
        apply hconf (K i) xhat hfr
        rw [norm_sub_rev, ← dist_eq_norm]
        exact hi
      obtain ⟨S, hS⟩ := Sol_pv_b3a67880_pigeon hev
      obtain ⟨i0, -, hTS⟩ := hS.exists
      intro w hw
      rw [hTS] at hw
      refine key S (hS.mono fun i h => h.1) (fun j hj => ?_) w hw
      have hdT : P.dir j ∈ tangentCone P.Ω xhat := by
        rw [hTS]
        refine ⟨fun k => if k = j then 1 else 0, fun k => by dsimp only; split_ifs <;> norm_num, ?_⟩
        simp [ite_smul, Finset.sum_ite_eq', hj, GPSSetup.dir]
      exact Sol_pv_b3a67880_poly P.A P.lo P.up xhat (P.dir j) hxhat hdT
        (fun i => R.x (K i)) (fun i => R.Δ (K i)) (fun i => hxΩ (K i)) (fun i => (hpos _).le)
        hlim hK.2.2
    · have hint : xhat ∈ interior P.Ω := by
        by_contra h
        exact hfr ⟨subset_closure hxhat, h⟩
      have hev : ∀ᶠ i in atTop, ∃ S, S = R.Dk (K i) := Eventually.of_forall fun i => ⟨_, rfl⟩
      obtain ⟨S, hS⟩ := Sol_pv_b3a67880_pigeon hev
      intro w _
      have hw : w ∈ nonnegSpan P.D S := by
        obtain ⟨i, rfl⟩ := hS.exists
        have := R.Dk_posSpanning (K i)
        unfold IsPositiveSpanning at this
        rw [this]
        trivial
      refine key S (hS.mono fun i h => h ▸ subset_rfl) (fun j _ => ?_) w hw
      have hpoll : Tendsto (fun i => R.x (K i) + R.Δ (K i) • P.dir j) atTop (𝓝 xhat) := by
        have := hlim.add (hK.2.2.smul_const (P.dir j))
        simpa using this
      exact (hpoll.eventually (isOpen_interior.mem_nhds hint)).mono fun i hi => interior_subset hi
  refine ⟨hfirst, ?_⟩
  show ∀ w ∈ tangentCone P.Ω xhat, -grad ⬝ᵥ w ≤ 0
  intro w hw
  rw [neg_dotProduct]
  linarith [hfirst w hw]
