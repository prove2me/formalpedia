-- Prove2me | solution 1 for BSUMConv.BSCA.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T20:21:44.299976+00:00
-- url     : https://prove2.me/submissions/09c226c6-7755-469d-a61d-1678c18fdded

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting
import Definitions.Def_BSUMConv_BSCA_Setting

set_option autoImplicit false

open TsengBCD.Stationary Filter Topology in
lemma bsca4_mem_Xset {N : ℕ} {n : Fin N → ℕ}
    {Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i)))} {y : X n} :
    y ∈ BSUMConv.BSUM.Xset Xs ↔ ∀ i, y i ∈ Xs i := by
  simp [BSUMConv.BSUM.Xset]

open TsengBCD.Stationary Filter Topology in
lemma bsca4_fext_in {N : ℕ} {n : Fin N → ℕ} {f : X n → ℝ} {S : Set (X n)} {z : X n}
    (hz : z ∈ S) : BSUMConv.BSCA.fext f S z = (f z : EReal) := by
  simp [BSUMConv.BSCA.fext, hz]

open TsengBCD.Stationary Filter Topology in
lemma bsca4_fext_out {N : ℕ} {n : Fin N → ℕ} {f : X n → ℝ} {S : Set (X n)} {z : X n}
    (hz : z ∉ S) : BSUMConv.BSCA.fext f S z = ⊤ := by
  simp [BSUMConv.BSCA.fext, hz]

lemma bsca4_alpha {β αinit : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 < αinit)
    (hα1 : αinit ≤ 1) (k : ℕ) : 0 < αinit * β ^ k ∧ αinit * β ^ k ≤ 1 := by
  refine ⟨mul_pos hα0 (pow_pos hβ0 k), ?_⟩
  calc αinit * β ^ k ≤ 1 * 1 :=
        mul_le_mul hα1 (pow_le_one₀ hβ0.le hβ1.le) (pow_pos hβ0 k).le zero_le_one
    _ = 1 := one_mul 1

open TsengBCD.Stationary BSUMConv.BSCA Filter Topology in
lemma bsca4_run_step {N : ℕ} {n : Fin N → ℕ}
    {Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i)))} {f : X n → ℝ}
    {h : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ}
    {s : ℕ → Fin N} {σ β αinit : ℝ} {x y : ℕ → X n} {j : ℕ → ℕ}
    (hrun : IsBSCARun Xs f h s σ β αinit x y j) (r : ℕ) (i : Fin N) (hi : s r = i) :
    y r i ∈ Xs i ∧ (∀ w ∈ Xs i, h i (y r i) (x r) ≤ h i w (x r)) ∧
      (∀ k, k ≠ i → y r k = x r k) ∧
      f (x r) - f (x r + (αinit * β ^ (j r)) • (y r - x r)) ≥
        -σ * (αinit * β ^ (j r)) * fderiv ℝ f (x r) (y r - x r) ∧
      (∀ j' : ℕ, j' < j r →
        ¬ (f (x r) - f (x r + (αinit * β ^ j') • (y r - x r)) ≥
          -σ * (αinit * β ^ j') * fderiv ℝ f (x r) (y r - x r))) ∧
      x (r + 1) = x r + (αinit * β ^ (j r)) • (y r - x r) := by
  subst hi
  exact hrun.2 r

open TsengBCD.Stationary BSUMConv.BSCA Filter Topology in
lemma bsca4_run_mem {N : ℕ} {n : Fin N → ℕ}
    {Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i)))} {f : X n → ℝ}
    {h : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ}
    {s : ℕ → Fin N} {σ β αinit : ℝ} {x y : ℕ → X n} {j : ℕ → ℕ}
    (hconvXs : ∀ i, Convex ℝ (Xs i))
    (hrun : IsBSCARun Xs f h s σ β αinit x y j)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 < αinit) (hα1 : αinit ≤ 1) :
    ∀ r, x r ∈ BSUMConv.BSUM.Xset Xs := by
  intro r
  induction r with
  | zero => exact hrun.1
  | succ r ih =>
    obtain ⟨h1, -, h3, -, -, h6⟩ := bsca4_run_step hrun r (s r) rfl
    obtain ⟨hA0, hA1⟩ := bsca4_alpha hβ0 hβ1 hα0 hα1 (j r)
    rw [bsca4_mem_Xset] at ih ⊢
    intro k
    rw [h6]
    by_cases hk : k = s r
    · subst hk
      have := (hconvXs _).add_smul_sub_mem (ih _) h1 ⟨hA0.le, hA1⟩
      simpa using this
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, h3 k hk, sub_self, smul_zero,
        add_zero]
      exact ih k

open TsengBCD.Stationary BSUMConv.BSCA Filter Topology in
lemma bsca4_d_single {N : ℕ} {n : Fin N → ℕ}
    {Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i)))} {f : X n → ℝ}
    {h : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ}
    {s : ℕ → Fin N} {σ β αinit : ℝ} {x y : ℕ → X n} {j : ℕ → ℕ}
    (hrun : IsBSCARun Xs f h s σ β αinit x y j) (r : ℕ) (i : Fin N) (hi : s r = i) :
    y r - x r = (Pi.single i ((y r - x r) i) : X n) := by
  obtain ⟨-, -, h3, -⟩ := bsca4_run_step hrun r i hi
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · rw [Pi.single_eq_of_ne hk]; simp [h3 k hk]

open TsengBCD.Stationary Filter Topology in
lemma bsca4_dirDeriv_le {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E} {φ : E → ℝ}
    (hφ : ConvexOn ℝ S φ) {a v : E} {c : ℝ} (hc : 0 < c) (ha : a ∈ S) (hav : a + c • v ∈ S) :
    dirDeriv (fun w => (φ w : EReal)) a v ≤ (((φ (a + c • v) - φ a) / c : ℝ) : EReal) := by
  unfold dirDeriv
  apply Filter.liminf_le_of_frequently_le _ (by isBoundedDefault)
  apply Eventually.frequently
  filter_upwards [Ioo_mem_nhdsGT hc] with t ht
  rw [← EReal.coe_sub, ← EReal.coe_mul]
  apply EReal.coe_le_coe_iff.2
  have ht0 := ht.1
  have hq0 : 0 ≤ 1 - t / c := by rw [sub_nonneg, div_le_one hc]; exact ht.2.le
  have hq1 : 0 ≤ t / c := (div_pos ht0 hc).le
  have hconv := hφ.2 ha hav hq0 hq1 (by ring)
  have e : (1 - t / c) • a + (t / c) • (a + c • v) = a + t • v := by
    rw [smul_add, smul_smul, div_mul_cancel₀ t hc.ne', sub_smul, one_smul]; abel
  rw [e, smul_eq_mul, smul_eq_mul] at hconv
  rw [mul_inv_le_iff₀ ht0, div_mul_eq_mul_div, le_div_iff₀ hc]
  have h2 : φ (a + t • v) * c ≤ ((1 - t / c) * φ a + t / c * φ (a + c • v)) * c :=
    mul_le_mul_of_nonneg_right hconv hc.le
  have e2 : ((1 - t / c) * φ a + t / c * φ (a + c • v)) * c =
      c * φ a - t * φ a + t * φ (a + c • v) := by
    field_simp
  linarith

open TsengBCD.Stationary Filter Topology in
lemma bsca4_dirDeriv_nonneg {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}
    (hS : Convex ℝ S) {φ : E → ℝ} {a v : E} (ha : a ∈ S) (hav : a + v ∈ S)
    (hmin : ∀ w ∈ S, φ a ≤ φ w) :
    0 ≤ dirDeriv (fun w => (φ w : EReal)) a v := by
  unfold dirDeriv
  apply Filter.le_liminf_of_le (by isBoundedDefault)
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  have hmem : a + t • v ∈ S := hS.add_smul_mem ha hav ⟨ht.1.le, ht.2.le⟩
  rw [← EReal.coe_sub, ← EReal.coe_mul]
  exact EReal.coe_nonneg.mpr
    (mul_nonneg (sub_nonneg.mpr (hmin _ hmem)) (inv_nonneg.mpr ht.1.le))

open TsengBCD.Stationary Filter Topology in
lemma bsca4_dirDeriv_neg {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E} {φ : E → ℝ}
    (hφ : StrictConvexOn ℝ S φ) {a v : E} (ha : a ∈ S) (hav : a + v ∈ S) (hv : v ≠ 0)
    (hle : φ (a + v) ≤ φ a) :
    dirDeriv (fun w => (φ w : EReal)) a v < 0 := by
  have hmid : a + (1/2 : ℝ) • v ∈ S := hφ.1.add_smul_mem ha hav ⟨by norm_num, by norm_num⟩
  have hne : a ≠ a + v := by simpa using hv
  have hlt : φ (a + (1/2 : ℝ) • v) < φ a := by
    have := hφ.2 ha hav hne (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
      (by norm_num)
    have e : (1/2 : ℝ) • a + (1/2 : ℝ) • (a + v) = a + (1/2 : ℝ) • v := by
      rw [smul_add, ← add_assoc, ← add_smul]; norm_num
    rw [e, smul_eq_mul, smul_eq_mul] at this
    linarith
  have h1 := bsca4_dirDeriv_le hφ.convexOn (by norm_num : (0:ℝ) < 1/2) ha hmid
  refine lt_of_le_of_lt h1 ?_
  have : (φ (a + (1/2:ℝ) • v) - φ a) / (1/2) < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by norm_num)
  exact_mod_cast this

open TsengBCD.Stationary BSUMConv.BSCA Filter Topology in
lemma bsca4_fderiv_le {N : ℕ} {n : Fin N → ℕ}
    {Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i)))} {f : X n → ℝ}
    {h : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ}
    {s : ℕ → Fin N} {σ β αinit : ℝ} {x y : ℕ → X n} {j : ℕ → ℕ}
    (hmatch : FirstOrderAgreement Xs f h) (hstrict : StrictApprox Xs h)
    (hm : ∀ r, x r ∈ BSUMConv.BSUM.Xset Xs)
    (hrun : IsBSCARun Xs f h s σ β αinit x y j) (r : ℕ) :
    fderiv ℝ f (x r) (y r - x r) ≤ 0 := by
  obtain ⟨h1, h2, -⟩ := bsca4_run_step hrun r (s r) rfl
  have hxX := bsca4_mem_Xset.1 (hm r)
  have hcv := (hstrict (s r) (x r) (hm r)).convexOn
  have e1 : x r (s r) + (1:ℝ) • (y r - x r) (s r) = y r (s r) := by simp
  have hle := bsca4_dirDeriv_le hcv one_pos (hxX (s r)) (by rw [e1]; exact h1)
  have hfo := hmatch (x r) (hm r) (s r) ((y r - x r) (s r)) (by simpa using h1)
  rw [hfo, e1, div_one] at hle
  rw [bsca4_d_single hrun r (s r) rfl]
  have := EReal.coe_le_coe_iff.1 hle
  linarith [h2 (x r (s r)) (hxX (s r))]

open TsengBCD.Stationary BSUMConv.BSCA Filter Topology in
lemma bsca4_f_desc {N : ℕ} {n : Fin N → ℕ}
    {Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i)))} {f : X n → ℝ}
    {h : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ}
    {s : ℕ → Fin N} {σ β αinit : ℝ} {x y : ℕ → X n} {j : ℕ → ℕ}
    (hmatch : FirstOrderAgreement Xs f h) (hstrict : StrictApprox Xs h)
    (hm : ∀ r, x r ∈ BSUMConv.BSUM.Xset Xs)
    (hσ0 : 0 < σ) (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 < αinit) (hα1 : αinit ≤ 1)
    (hrun : IsBSCARun Xs f h s σ β αinit x y j) (r : ℕ) :
    f (x (r + 1)) ≤ f (x r) := by
  obtain ⟨-, -, -, h4, -, h6⟩ := bsca4_run_step hrun r (s r) rfl
  have hA := bsca4_alpha hβ0 hβ1 hα0 hα1 (j r)
  have hD := bsca4_fderiv_le hmatch hstrict hm hrun r
  rw [h6]
  have : 0 ≤ -σ * (αinit * β ^ j r) * fderiv ℝ f (x r) (y r - x r) := by
    have e : -σ * (αinit * β ^ j r) * fderiv ℝ f (x r) (y r - x r) =
        σ * (αinit * β ^ j r) * (-fderiv ℝ f (x r) (y r - x r)) := by ring
    rw [e]; exact mul_nonneg (mul_nonneg hσ0.le hA.1.le) (by linarith)
  linarith

open TsengBCD.Stationary BSUMConv.BSCA Filter Topology in
lemma bsca4_u_tendsto {N : ℕ} {n : Fin N → ℕ}
    {Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i)))}
    {h : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ}
    (hcont : ContinuousApprox Xs h) (i : Fin N) {F : Filter ℕ}
    {a : ℕ → EuclideanSpace ℝ (Fin (n i))} {y : ℕ → X n}
    {a0 : EuclideanSpace ℝ (Fin (n i))} {y0 : X n}
    (ha : Tendsto a F (𝓝 a0)) (hy : Tendsto y F (𝓝 y0)) (ha0 : a0 ∈ Xs i)
    (hy0 : y0 ∈ BSUMConv.BSUM.Xset Xs) (haX : ∀ᶠ r in F, a r ∈ Xs i)
    (hyX : ∀ᶠ r in F, y r ∈ BSUMConv.BSUM.Xset Xs) :
    Tendsto (fun r => h i (a r) (y r)) F (𝓝 (h i a0 y0)) :=
  ((hcont i) (a0, y0) ⟨ha0, hy0⟩).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨ha.prodMk_nhds hy, (haX.and hyX).mono fun _ h => ⟨h.1, h.2⟩⟩)

open TsengBCD.Stationary BSUMConv.BSCA Filter Topology in
lemma bsca4_key {N : ℕ} {n : Fin N → ℕ}
    {Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i)))} {f : X n → ℝ}
    {h : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ}
    {s : ℕ → Fin N} {σ β αinit : ℝ} {x y : ℕ → X n} {j : ℕ → ℕ}
    (hclosed : ∀ i, IsClosed (Xs i)) (hconvXs : ∀ i, Convex ℝ (Xs i))
    (hC1 : ContDiff ℝ 1 f) (hmatch : FirstOrderAgreement Xs f h)
    (hstrict : StrictApprox Xs h) (hcont : ContinuousApprox Xs h)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα0 : 0 < αinit) (hα1 : αinit ≤ 1)
    (hrun : IsBSCARun Xs f h s σ β αinit x y j)
    (hdec : Tendsto (fun r => f (x r) - f (x (r + 1))) atTop (𝓝 0))
    {z : X n} (hzX : z ∈ BSUMConv.BSUM.Xset Xs)
    (U : Ultrafilter ℕ) (g : ℕ → ℕ) (hg : Tendsto g (U : Filter ℕ) atTop) (i : Fin N)
    (hgi : ∀ᶠ r in (U : Filter ℕ), s (g r) = i)
    (hx : Tendsto (fun r => x (g r)) (U : Filter ℕ) (𝓝 z)) :
    Tendsto (fun r => x (g r + 1)) (U : Filter ℕ) (𝓝 z) ∧
      ∀ v ∈ Xs i, h i (z i) z ≤ h i v z := by
  have hm := bsca4_run_mem hconvXs hrun hβ0 hβ1 hα0 hα1
  have hzX' := bsca4_mem_Xset.1 hzX
  set dd : ℕ → X n := fun r => y (g r) - x (g r) with hdd
  set M : ℕ → ℝ := fun r => max 1 ‖dd r‖ with hM
  have hM1 : ∀ r, 1 ≤ M r := fun r => le_max_left _ _
  have hMpos : ∀ r, 0 < M r := fun r => zero_lt_one.trans_le (hM1 r)
  set w : ℕ → X n := fun r => (M r)⁻¹ • dd r with hw
  have hwn : ∀ r, ‖w r‖ ≤ 1 := by
    intro r
    show ‖(M r)⁻¹ • dd r‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hMpos r), inv_mul_le_iff₀ (hMpos r),
      mul_one]
    exact le_max_right _ _
  have hdf : Tendsto (fun r => f (x (g r)) - f (x (g r + 1))) (U : Filter ℕ) (𝓝 0) :=
    hdec.comp hg
  have hfd : Continuous (fderiv ℝ f) := hC1.continuous_fderiv one_ne_zero
  have happ : ∀ {p : ℕ → X n} {v : ℕ → X n} {p0 v0 : X n},
      Tendsto p (U : Filter ℕ) (𝓝 p0) → Tendsto v (U : Filter ℕ) (𝓝 v0) →
      Tendsto (fun r => fderiv ℝ f (p r) (v r)) (U : Filter ℕ) (𝓝 (fderiv ℝ f p0 v0)) := by
    intro p v p0 v0 hp hv
    exact (isBoundedBilinearMap_apply.continuous.tendsto (fderiv ℝ f p0, v0)).comp
      (((hfd.tendsto p0).comp hp).prodMk_nhds hv)
  have hseg : ∀ᶠ r in (U : Filter ℕ), x (g r) i + w r i ∈ Xs i ∧
      h i (x (g r) i + w r i) (x (g r)) ≤ h i (x (g r) i) (x (g r)) := by
    filter_upwards [hgi] with r hri
    obtain ⟨h1, h2, -⟩ := bsca4_run_step hrun (g r) i hri
    have hxX := bsca4_mem_Xset.1 (hm (g r))
    have hcs := ((hstrict i (x (g r)) (hm (g r))).convexOn).convex_le (h i (x (g r) i) (x (g r)))
    have hθ : (M r)⁻¹ ∈ Set.Icc (0:ℝ) 1 :=
      ⟨(inv_pos.2 (hMpos r)).le, inv_le_one_of_one_le₀ (hM1 r)⟩
    have := hcs.add_smul_sub_mem ⟨hxX i, le_rfl⟩ ⟨h1, h2 _ (hxX i)⟩ hθ
    have e : w r i = (M r)⁻¹ • (y (g r) i - x (g r) i) := rfl
    rw [e]
    exact this
  obtain ⟨wb, -, hwbt⟩ := (isCompact_closedBall (0 : X n) 1).ultrafilter_le_nhds (U.map w)
    (by
      rw [Ultrafilter.coe_map, le_principal_iff]
      exact Filter.mem_map.2 (Filter.univ_mem' fun r => mem_closedBall_zero_iff.2 (hwn r)))
  have hwt : Tendsto w (U : Filter ℕ) (𝓝 wb) := by
    rw [Ultrafilter.coe_map] at hwbt; exact hwbt
  have hwb0 : wb = 0 := by
    by_contra hne
    have hoff : ∀ k, k ≠ i → wb k = 0 := by
      intro k hk
      have h1 : Tendsto (fun r => w r k) (U : Filter ℕ) (𝓝 (wb k)) :=
        ((continuous_apply k).tendsto wb).comp hwt
      have h2 : ∀ᶠ r in (U : Filter ℕ), w r k = 0 := by
        filter_upwards [hgi] with r hri
        obtain ⟨-, -, h3, -⟩ := bsca4_run_step hrun (g r) i hri
        show (M r)⁻¹ • (y (g r) k - x (g r) k) = 0
        rw [h3 k hk, sub_self, smul_zero]
      exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' (h2.mono fun r hr => hr.symm))
    have hwbs : wb = (Pi.single i (wb i) : X n) := by
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · rw [Pi.single_eq_of_ne hk]; exact hoff k hk
    have hwbi : wb i ≠ 0 := by
      intro h0; apply hne; rw [hwbs, h0]; simp
    have hxi : Tendsto (fun r => x (g r) i) (U : Filter ℕ) (𝓝 (z i)) :=
      ((continuous_apply i).tendsto z).comp hx
    have hpt : Tendsto (fun r => x (g r) i + w r i) (U : Filter ℕ) (𝓝 (z i + wb i)) :=
      hxi.add (((continuous_apply i).tendsto wb).comp hwt)
    have hpmem : z i + wb i ∈ Xs i :=
      (hclosed i).mem_of_tendsto hpt (hseg.mono fun _ h => h.1)
    have hl1 := bsca4_u_tendsto hcont i hpt hx hpmem hzX (hseg.mono fun _ h => h.1)
      (Eventually.of_forall fun r => hm _)
    have hl2 := bsca4_u_tendsto hcont i hxi hx (hzX' i) hzX
      (Eventually.of_forall fun r => bsca4_mem_Xset.1 (hm _) i)
      (Eventually.of_forall fun r => hm _)
    have hle : h i (z i + wb i) z ≤ h i (z i) z :=
      le_of_tendsto_of_tendsto hl1 hl2 (hseg.mono fun _ h => h.2)
    have hneg : fderiv ℝ f z wb < 0 := by
      have := bsca4_dirDeriv_neg (hstrict i z hzX) (hzX' i) hpmem hwbi hle
      rw [hmatch z hzX i (wb i) hpmem] at this
      rw [hwbs]
      exact_mod_cast this
    obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = -fderiv ℝ f z wb := ⟨_, rfl⟩
    have hγ0 : 0 < γ := by rw [hγ]; linarith
    have hFw : Tendsto (fun r => fderiv ℝ f (x (g r)) (w r)) (U : Filter ℕ) (𝓝 (-γ)) := by
      rw [hγ, neg_neg]; exact happ hx hwt
    have hFzw : Tendsto (fun r => fderiv ℝ f z (w r)) (U : Filter ℕ) (𝓝 (-γ)) := by
      rw [hγ, neg_neg]; exact ((fderiv ℝ f z).continuous.tendsto wb).comp hwt
    have hFdd : ∀ r, fderiv ℝ f (x (g r)) (dd r) = M r * fderiv ℝ f (x (g r)) (w r) := by
      intro r
      show _ = M r * fderiv ℝ f (x (g r)) ((M r)⁻¹ • dd r)
      rw [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (hMpos r).ne', one_mul]
    have hev1 : ∀ᶠ r in (U : Filter ℕ), γ / 2 < -fderiv ℝ f (x (g r)) (w r) := by
      have := hFw.neg
      rw [neg_neg] at this
      exact this.eventually (lt_mem_nhds (by linarith))
    set lam : ℕ → ℝ := fun r => αinit * β ^ (j (g r)) * M r with hlam
    have hlam_pos : ∀ r, 0 < lam r := fun r =>
      mul_pos (bsca4_alpha hβ0 hβ1 hα0 hα1 _).1 (hMpos r)
    have hlam_le : ∀ᶠ r in (U : Filter ℕ),
        lam r ≤ (2 / (σ * γ)) * (f (x (g r)) - f (x (g r + 1))) := by
      filter_upwards [hgi, hev1] with r hri hr
      obtain ⟨-, -, -, h4, -, h6⟩ := bsca4_run_step hrun (g r) i hri
      rw [h6]
      have h4' : f (x (g r)) - f (x (g r) + (αinit * β ^ j (g r)) • (y (g r) - x (g r))) ≥
          σ * lam r * (-fderiv ℝ f (x (g r)) (w r)) := by
        have h4c := h4
        rw [show y (g r) - x (g r) = dd r from rfl, hFdd r] at h4c
        rw [show y (g r) - x (g r) = dd r from rfl]
        have e : -σ * (αinit * β ^ j (g r)) * (M r * fderiv ℝ f (x (g r)) (w r)) =
            σ * lam r * (-fderiv ℝ f (x (g r)) (w r)) := by
          simp only [hlam]; ring
        linarith
      have hp := mul_le_mul_of_nonneg_left hr.le (mul_pos hσ0 (hlam_pos r)).le
      rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos hσ0 hγ0)]
      nlinarith
    have hlam0 : Tendsto lam (U : Filter ℕ) (𝓝 0) := by
      have hup : Tendsto (fun r => (2 / (σ * γ)) * (f (x (g r)) - f (x (g r + 1))))
          (U : Filter ℕ) (𝓝 0) := by
        simpa using hdf.const_mul (2 / (σ * γ))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
        (Eventually.of_forall fun r => (hlam_pos r).le) hlam_le
    have hfail : ∀ᶠ r in (U : Filter ℕ),
        f (x (g r) + (lam r / β) • w r) - f (x (g r)) >
          σ * (lam r / β) * fderiv ℝ f (x (g r)) (w r) := by
      have hsmall : ∀ᶠ r in (U : Filter ℕ), lam r < αinit := hlam0.eventually (gt_mem_nhds hα0)
      filter_upwards [hgi, hsmall] with r hri hr
      obtain ⟨-, -, -, -, h5, -⟩ := bsca4_run_step hrun (g r) i hri
      have hj : j (g r) ≠ 0 := by
        intro h0
        have : lam r = αinit * M r := by simp only [hlam, h0, pow_zero, mul_one]
        rw [this] at hr
        nlinarith [hM1 r]
      have hpow : β ^ (j (g r) - 1) * β = β ^ (j (g r)) := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj)]
      have h5' := h5 (j (g r) - 1) (by omega)
      have hβne := hβ0.ne'
      have hMne := (hMpos r).ne'
      have hc : lam r / β * (M r)⁻¹ = αinit * β ^ (j (g r) - 1) := by
        simp only [hlam]; rw [← hpow]; field_simp
      have hc2 : αinit * β ^ (j (g r) - 1) * M r = lam r / β := by
        rw [← hc]; field_simp
      have e1 : (αinit * β ^ (j (g r) - 1)) • (y (g r) - x (g r)) = (lam r / β) • w r := by
        show _ = (lam r / β) • ((M r)⁻¹ • dd r)
        rw [smul_smul, hc]
      have e2 : -σ * (αinit * β ^ (j (g r) - 1)) * fderiv ℝ f (x (g r)) (y (g r) - x (g r)) =
          -(σ * (lam r / β) * fderiv ℝ f (x (g r)) (w r)) := by
        rw [show y (g r) - x (g r) = dd r from rfl, hFdd r, ← hc2]; ring
      rw [e1, e2] at h5'
      rw [not_le] at h5'
      linarith
    have hε0 : 0 < (1 - σ) * γ / 3 := div_pos (mul_pos (by linarith) hγ0) (by norm_num)
    have hsd : HasStrictFDerivAt f (fderiv ℝ f z) z :=
      hC1.contDiffAt.hasStrictFDerivAt one_ne_zero
    have hlo := (hasStrictFDerivAt_iff_isLittleO.1 hsd).def hε0
    have hμw : Tendsto (fun r => (lam r / β) • w r) (U : Filter ℕ) (𝓝 0) := by
      refine squeeze_zero_norm (a := fun r => lam r / β) (fun r => ?_)
        (by simpa using hlam0.div_const β)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (hlam_pos r) hβ0)]
      exact mul_le_of_le_one_right (div_pos (hlam_pos r) hβ0).le (hwn r)
    have hpair : Tendsto (fun r => (x (g r) + (lam r / β) • w r, x (g r))) (U : Filter ℕ)
        (𝓝 (z, z)) := by
      have := hx.add hμw
      rw [add_zero] at this
      exact this.prodMk_nhds hx
    have hB := hpair.eventually hlo
    have hC := hFzw.eventually (gt_mem_nhds (show -γ < -γ + (1 - σ) * γ / 3 by linarith))
    have hD := hFw.eventually (lt_mem_nhds (show -γ - (1 - σ) * γ / 3 < -γ by linarith))
    obtain ⟨r, hr1, hr2, hr3, hr4⟩ := (hfail.and (hB.and (hC.and hD))).exists
    simp only [add_sub_cancel_left] at hr2
    have hμ : 0 < lam r / β := div_pos (hlam_pos r) hβ0
    rw [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hμ]
      at hr2
    have hab := (abs_le.1 hr2).2
    have hwr := hwn r
    have p1 := mul_pos (mul_pos hσ0 hμ)
      (show 0 < fderiv ℝ f (x (g r)) (w r) + γ + (1 - σ) * γ / 3 by linarith)
    have p2 := mul_le_mul_of_nonneg_left hwr (mul_pos hε0 hμ).le
    have p3 := mul_lt_mul_of_pos_left hr3 hμ
    have p4 := mul_pos hμ (mul_pos (mul_pos (show (0:ℝ) < 1 - σ by linarith)
      (show (0:ℝ) < 1 - σ by linarith)) hγ0)
    nlinarith
  have hwt0 : Tendsto w (U : Filter ℕ) (𝓝 0) := hwb0 ▸ hwt
  have hww : ∀ᶠ r in (U : Filter ℕ), w r = dd r := by
    have := (tendsto_norm_zero.comp hwt0).eventually (gt_mem_nhds one_pos)
    filter_upwards [this] with r hr
    have hr' : ‖w r‖ < 1 := hr
    have hle : ‖dd r‖ ≤ 1 := by
      by_contra hgt
      rw [not_le] at hgt
      have hMr : M r = ‖dd r‖ := max_eq_right hgt.le
      have h1 : ‖w r‖ = 1 := by
        show ‖(M r)⁻¹ • dd r‖ = 1
        rw [norm_smul, hMr, Real.norm_eq_abs, abs_inv, abs_of_pos (by linarith),
          inv_mul_cancel₀ (by linarith)]
      linarith
    have hMr : M r = 1 := max_eq_left hle
    show (M r)⁻¹ • dd r = dd r
    rw [hMr, inv_one, one_smul]
  have hdd0 : Tendsto dd (U : Filter ℕ) (𝓝 0) := hwt0.congr' hww
  refine ⟨?_, ?_⟩
  · have hstep : Tendsto (fun r => (αinit * β ^ (j (g r))) • dd r) (U : Filter ℕ) (𝓝 0) := by
      refine squeeze_zero_norm (a := fun r => ‖dd r‖) (fun r => ?_)
        (tendsto_norm_zero.comp hdd0)
      obtain ⟨hA0, hA1⟩ := bsca4_alpha hβ0 hβ1 hα0 hα1 (j (g r))
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hA0]
      exact mul_le_of_le_one_left (norm_nonneg _) hA1
    have := hx.add hstep
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [hgi] with r hri
    exact ((bsca4_run_step hrun (g r) i hri).2.2.2.2.2).symm
  · intro v hv
    have hy : Tendsto (fun r => y (g r)) (U : Filter ℕ) (𝓝 z) := by
      have := hx.add hdd0
      rw [add_zero] at this
      refine this.congr' (Eventually.of_forall fun r => ?_)
      show x (g r) + (y (g r) - x (g r)) = y (g r)
      abel
    have hyi := ((continuous_apply i).tendsto z).comp hy
    have hl := bsca4_u_tendsto hcont i hyi hx (hzX' i) hzX
      (hgi.mono fun r hri => (bsca4_run_step hrun (g r) i hri).1)
      (Eventually.of_forall fun r => hm _)
    have hr := bsca4_u_tendsto hcont i (tendsto_const_nhds (x := v)) hx hv hzX
      (Eventually.of_forall fun _ => hv) (Eventually.of_forall fun r => hm _)
    exact le_of_tendsto_of_tendsto hl hr
      (hgi.mono fun r hri => (bsca4_run_step hrun (g r) i hri).2.1 v hv)

-- Theorem 4, p. 18: every limit point of cyclic BSCA is stationary for (12).
open Filter Topology TsengBCD.Stationary BSUMConv.BSCA in
theorem solution {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (f : X n → ℝ)
    (h : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ)
    (s : ℕ → Fin N) (σ β αinit : ℝ) (x y : ℕ → X n) (j : ℕ → ℕ)
    (hclosed : ∀ i, IsClosed (Xs i)) (hconvXs : ∀ i, Convex ℝ (Xs i))
    (hnonempty : ∀ i, (Xs i).Nonempty)
    (hC1 : ContDiff ℝ 1 f) (hmatch : FirstOrderAgreement Xs f h)
    (hstrict : StrictApprox Xs h) (hcont : ContinuousApprox Xs h)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα0 : 0 < αinit) (hα1 : αinit ≤ 1)
    (hcyclic : IsCyclic s) (hrun : IsBSCARun Xs f h s σ β αinit x y j) :
    ∀ z : X n, MapClusterPt z atTop x → IsStationary (fext f (BSUMConv.BSUM.Xset Xs)) z := by
  intro z hz
  have hm := bsca4_run_mem hconvXs hrun hβ0 hβ1 hα0 hα1
  have hXc : IsClosed (BSUMConv.BSUM.Xset Xs) := isClosed_set_pi fun i _ => hclosed i
  have hXconv : Convex ℝ (BSUMConv.BSUM.Xset Xs) := convex_pi fun i _ => hconvXs i
  have hzX : z ∈ BSUMConv.BSUM.Xset Xs := hXc.mem_of_mapClusterPt hz (Eventually.of_forall hm)
  have hzX' := bsca4_mem_Xset.1 hzX
  have hfc : Continuous f := hC1.continuous
  have hdesc : ∀ r, f (x (r + 1)) ≤ f (x r) :=
    bsca4_f_desc hmatch hstrict hm hσ0 hβ0 hβ1 hα0 hα1 hrun
  have hanti : Antitone (fun r => f (x r)) := antitone_nat_of_succ_le hdesc
  have hlow : ∀ r, f z ≤ f (x r) := by
    intro r
    have hS : IsClosed (f ⁻¹' Set.Iic (f (x r))) := isClosed_Iic.preimage hfc
    exact hS.mem_of_mapClusterPt hz ((eventually_ge_atTop r).mono fun r' hr' => hanti hr')
  have hL := tendsto_atTop_ciInf hanti ⟨f z, by rintro _ ⟨r, rfl⟩; exact hlow r⟩
  have hdec : Tendsto (fun r => f (x r) - f (x (r + 1))) atTop (𝓝 0) := by
    have h2 := (tendsto_add_atTop_iff_nat 1).2 hL
    simpa using hL.sub h2
  obtain ⟨U, hUle, hUx⟩ := mapClusterPt_iff_ultrafilter.1 hz
  obtain ⟨a, ha⟩ := (U.map s).eq_pure_of_finite
  have hsa : ∀ᶠ r in (U : Filter ℕ), s r = a := by
    have h : ({a} : Set (Fin N)) ∈ U.map s := by
      rw [ha]; exact Ultrafilter.mem_pure.2 rfl
    exact Ultrafilter.mem_map.1 h
  have hNpos : 0 < N := a.pos
  have hshift : ∀ m : ℕ, ∀ᶠ r in (U : Filter ℕ), (s (r + m) : ℕ) = ((a : ℕ) + m) % N := by
    intro m
    filter_upwards [hsa] with r hr
    rw [hcyclic, Nat.add_mod, ← hcyclic r, hr]
    conv_rhs => rw [Nat.add_mod, Nat.mod_eq_of_lt a.isLt]
  have hgm : ∀ m : ℕ, Tendsto (fun r => r + m) (U : Filter ℕ) atTop :=
    fun m => (tendsto_add_atTop_nat m).mono_left hUle
  have hconv : ∀ m : ℕ, Tendsto (fun r => x (r + m)) (U : Filter ℕ) (𝓝 z) := by
    intro m
    induction m with
    | zero => simpa using hUx
    | succ m ih =>
      have := (bsca4_key hclosed hconvXs hC1 hmatch hstrict hcont hσ0 hσ1 hβ0 hβ1 hα0 hα1
        hrun hdec hzX U (fun r => r + m) (hgm m) ⟨((a : ℕ) + m) % N, Nat.mod_lt _ hNpos⟩
        ((hshift m).mono fun r hr => Fin.ext hr) ih).1
      simpa [add_assoc] using this
  have hcs : ∀ (k : Fin N) (dk : EuclideanSpace ℝ (Fin (n k))), z k + dk ∈ Xs k →
      0 ≤ fderiv ℝ f z (Pi.single k dk) := by
    intro k dk hk
    set m : ℕ := N - (a : ℕ) + k with hmdef
    have hsk : ∀ᶠ r in (U : Filter ℕ), s (r + m) = k := by
      filter_upwards [hshift m] with r hr
      apply Fin.ext
      rw [hr, show (a : ℕ) + m = k + N by have := a.isLt; omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt k.isLt]
    have hmin := (bsca4_key hclosed hconvXs hC1 hmatch hstrict hcont hσ0 hσ1 hβ0 hβ1 hα0 hα1
      hrun hdec hzX U (fun r => r + m) (hgm m) k hsk (hconv m)).2
    have := bsca4_dirDeriv_nonneg (φ := fun v => h k v z) (hconvXs k) (hzX' k) hk hmin
    rw [hmatch z hzX k dk hk] at this
    exact_mod_cast this
  refine ⟨?_, fun d => ?_⟩
  · rw [bsca4_fext_in hzX]; exact EReal.coe_ne_top _
  · by_cases hex : ∃ t0 : ℝ, 0 < t0 ∧ z + t0 • d ∈ BSUMConv.BSUM.Xset Xs
    · obtain ⟨t0, ht0, hmem⟩ := hex
      have hmem' := bsca4_mem_Xset.1 hmem
      have hnn : 0 ≤ fderiv ℝ f z d := by
        have hsum : d = ∑ k, (Pi.single k (d k) : X n) := (Finset.univ_sum_single d).symm
        rw [hsum, map_sum]
        refine Finset.sum_nonneg fun k _ => ?_
        have h1 := hcs k (t0 • d k) (by simpa using hmem' k)
        rw [Pi.single_smul, map_smul, smul_eq_mul] at h1
        exact (mul_nonneg_iff_of_pos_left ht0).1 h1
      have h1 : HasDerivAt (fun t : ℝ => z + t • d) d 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add z
      have h2 : HasFDerivAt f (fderiv ℝ f z) (z + (0:ℝ) • d) := by
        rw [zero_smul, add_zero]; exact (hC1.differentiable one_ne_zero z).hasFDerivAt
      have hder : HasDerivAt (fun t : ℝ => f (z + t • d)) (fderiv ℝ f z d) 0 :=
        h2.comp_hasDerivAt (0:ℝ) h1
      have hsl := hder.tendsto_slope_zero_right
      simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at hsl
      have hE : Tendsto (fun t : ℝ => (fext f (BSUMConv.BSUM.Xset Xs) (z + t • d) -
          fext f (BSUMConv.BSUM.Xset Xs) z) * ((t⁻¹ : ℝ) : EReal)) (𝓝[>] 0)
          (𝓝 ((fderiv ℝ f z d : ℝ) : EReal)) := by
        have hc := (continuous_coe_real_ereal.tendsto _).comp hsl
        refine hc.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT ht0] with t ht
        have hmt : z + t • d ∈ BSUMConv.BSUM.Xset Xs := by
          have := hXconv.add_smul_mem hzX hmem
            ⟨(div_pos ht.1 ht0).le, (div_le_one ht0).2 ht.2.le⟩
          rwa [smul_smul, div_mul_cancel₀ t ht0.ne'] at this
        rw [bsca4_fext_in hmt, bsca4_fext_in hzX, ← EReal.coe_sub, ← EReal.coe_mul]
        simp only [Function.comp_apply]
        congr 1
        ring
      unfold dirDeriv
      rw [hE.liminf_eq]
      exact_mod_cast hnn
    · simp only [not_exists, not_and] at hex
      unfold dirDeriv
      apply Filter.le_liminf_of_le (by isBoundedDefault)
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      rw [bsca4_fext_out (hex t ht), bsca4_fext_in hzX, EReal.top_sub_coe,
        EReal.top_mul_of_pos (by exact_mod_cast inv_pos.2 ht)]
      exact le_top
