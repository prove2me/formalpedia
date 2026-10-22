-- Prove2me | solution 1 for BSUMConv.BSUM.theorem_2_a
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T18:53:09.53874+00:00
-- url     : https://prove2.me/submissions/996c103d-e6cc-44f5-9f4b-648d4b926031

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting
import Definitions.Def_BSUMConv_BSUM_Setting

set_option autoImplicit false

open TsengBCD.Stationary BSUMConv.BSUM Filter Topology in
lemma bsum2a_mem_Xset {N : ℕ} {n : Fin N → ℕ}
    {Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i)))} {y : X n} :
    y ∈ Xset Xs ↔ ∀ i, y i ∈ Xs i := by
  simp [Xset]

open TsengBCD.Stationary BSUMConv.BSUM Filter Topology in
lemma bsum2a_run_step {N : ℕ} {n : Fin N → ℕ}
    {Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i)))}
    {u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ} {s : ℕ → Fin N} {x : ℕ → X n}
    (hx : IsBSUMRun Xs u s x) (r : ℕ) (i : Fin N) (h : s r = i) :
    x (r + 1) i ∈ Xs i ∧ (∀ w ∈ Xs i, u i (x (r + 1) i) (x r) ≤ u i w (x r)) ∧
      ∀ k, k ≠ i → x (r + 1) k = x r k := by
  subst h
  exact hx.2 r

open TsengBCD.Stationary BSUMConv.BSUM Filter Topology in
lemma bsum2a_run_mem {N : ℕ} {n : Fin N → ℕ}
    {Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i)))}
    {u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ} {s : ℕ → Fin N} {x : ℕ → X n}
    (hx : IsBSUMRun Xs u s x) : ∀ r, x r ∈ Xset Xs := by
  intro r
  induction r with
  | zero => exact hx.1
  | succ r ih =>
    obtain ⟨h1, -, h3⟩ := bsum2a_run_step hx r (s r) rfl
    rw [bsum2a_mem_Xset] at ih ⊢
    intro k
    by_cases hk : k = s r
    · subst hk; exact h1
    · rw [h3 k hk]; exact ih k

open TsengBCD.Stationary BSUMConv.BSUM Filter Topology in
lemma bsum2a_run_update {N : ℕ} {n : Fin N → ℕ}
    {Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i)))}
    {u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ} {s : ℕ → Fin N} {x : ℕ → X n}
    (hx : IsBSUMRun Xs u s x) (r : ℕ) (i : Fin N) (h : s r = i) :
    x (r + 1) = Function.update (x r) i (x (r + 1) i) := by
  obtain ⟨-, -, h3⟩ := bsum2a_run_step hx r i h
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · rw [Function.update_of_ne hk]; exact h3 k hk

open TsengBCD.Stationary BSUMConv.BSUM Filter Topology in
lemma bsum2a_f_le_u {N : ℕ} {n : Fin N → ℕ}
    {Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i)))} {f : X n → ℝ}
    {u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ} {s : ℕ → Fin N} {x : ℕ → X n}
    (hA2 : Assumption2 Xs f u) (hx : IsBSUMRun Xs u s x) (r : ℕ) (i : Fin N) (h : s r = i) :
    f (x (r + 1)) ≤ u i (x (r + 1) i) (x r) := by
  obtain ⟨h1, -, -⟩ := bsum2a_run_step hx r i h
  have := hA2.B2 i _ h1 (x r) (bsum2a_run_mem hx r)
  rwa [← bsum2a_run_update hx r i h] at this

open TsengBCD.Stationary BSUMConv.BSUM Filter Topology in
lemma bsum2a_u_tendsto {N : ℕ} {n : Fin N → ℕ}
    {Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i)))} {f : X n → ℝ}
    {u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ}
    (hA2 : Assumption2 Xs f u) (i : Fin N) {F : Filter ℕ}
    {a : ℕ → EuclideanSpace ℝ (Fin (n i))} {y : ℕ → X n}
    {a0 : EuclideanSpace ℝ (Fin (n i))} {y0 : X n}
    (ha : Tendsto a F (𝓝 a0)) (hy : Tendsto y F (𝓝 y0)) (ha0 : a0 ∈ Xs i)
    (hy0 : y0 ∈ Xset Xs) (haX : ∀ᶠ r in F, a r ∈ Xs i) (hyX : ∀ᶠ r in F, y r ∈ Xset Xs) :
    Tendsto (fun r => u i (a r) (y r)) F (𝓝 (u i a0 y0)) :=
  ((hA2.B4 i) (a0, y0) ⟨ha0, hy0⟩).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨ha.prodMk_nhds hy, (haX.and hyX).mono fun _ h => ⟨h.1, h.2⟩⟩)

open TsengBCD.Stationary BSUMConv.BSUM Filter Topology in
lemma bsum2a_dirDeriv_nonneg_of_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    (h : V → EReal) (x d : V) {c : ℝ} (hc : 0 < c) (H : 0 ≤ dirDeriv h x (c • d)) :
    0 ≤ dirDeriv h x d := by
  unfold dirDeriv at *
  rw [le_liminf_iff] at H ⊢
  intro y hy
  obtain ⟨y0, hyy0, hy00⟩ := EReal.lt_iff_exists_real_btwn.1 hy
  have hy0 : y0 < 0 := by exact_mod_cast hy00
  have h1 := H ((y0 * c : ℝ) : EReal) (by exact_mod_cast mul_neg_of_neg_of_pos hy0 hc)
  have hmap : Tendsto (fun s : ℝ => s / c) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun s : ℝ => s / c) (𝓝 0) (𝓝 (0 / c)) :=
        (continuous_id.div_const c).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
      exact div_pos hs hc
  filter_upwards [hmap.eventually h1, self_mem_nhdsWithin] with s hs (hs0 : 0 < s)
  have e1 : (s / c) • (c • d) = s • d := by
    rw [smul_smul, div_mul_cancel₀ s hc.ne']
  have e2 : (s / c)⁻¹ = s⁻¹ * c := by
    field_simp
  simp only [e1, e2, EReal.coe_mul, ← mul_assoc] at hs
  generalize (h (x + s • d) - h x) * ((s⁻¹ : ℝ) : EReal) = w at hs ⊢
  have key : (y0 : EReal) < w := by
    induction w using EReal.rec with
    | bot =>
      rw [EReal.bot_mul_of_pos (by exact_mod_cast hc)] at hs
      exact absurd hs not_lt_bot
    | top => exact EReal.coe_lt_top _
    | coe a =>
      rw [← EReal.coe_mul] at hs
      have := EReal.coe_lt_coe_iff.1 hs
      exact EReal.coe_lt_coe_iff.2 (lt_of_mul_lt_mul_right this hc.le)
  exact hyy0.trans key

open TsengBCD.Stationary BSUMConv.BSUM Filter Topology in
lemma bsum2a_step {N : ℕ} {n : Fin N → ℕ}
    {Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i)))}
    (hXclosed : ∀ i, IsClosed (Xs i))
    {f : X n → ℝ} (hf : ContinuousOn f (Xset Xs))
    {u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ} (hA2 : Assumption2 Xs f u)
    (hqc : BlockQuasiconvex Xs u) (huniq : ∀ i, UniqueBlockMin Xs u i)
    {s : ℕ → Fin N} {x : ℕ → X n} (hx : IsBSUMRun Xs u s x)
    {z : X n} (hzX : z ∈ Xset Xs) (hlow : ∀ r, f z ≤ f (x r))
    (U : Ultrafilter ℕ) (g : ℕ → ℕ) (i : Fin N) (hgi : ∀ᶠ r in (U : Filter ℕ), s (g r) = i)
    (hg : Tendsto (fun r => x (g r)) (U : Filter ℕ) (𝓝 z)) :
    Tendsto (fun r => x (g r + 1)) (U : Filter ℕ) (𝓝 z) := by
  have hm := bsum2a_run_mem hx
  have hzX' := bsum2a_mem_Xset.1 hzX
  have hgi' : Tendsto (fun r => x (g r) i) (U : Filter ℕ) (𝓝 (z i)) :=
    ((continuous_apply i).tendsto z).comp hg
  have hfx : Tendsto (fun r => f (x (g r))) (U : Filter ℕ) (𝓝 (f z)) :=
    (hf z hzX).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hg, Eventually.of_forall fun r => hm _⟩)
  set v : ℕ → EuclideanSpace ℝ (Fin (n i)) := fun r => x (g r + 1) i - x (g r) i with hv
  have hv0 : Tendsto v (U : Filter ℕ) (𝓝 0) := by
    by_contra hcon
    rw [Metric.tendsto_nhds] at hcon
    push_neg at hcon
    obtain ⟨ε, hε, hfreq⟩ := hcon
    have hbig : ∀ᶠ r in (U : Filter ℕ), ε ≤ ‖v r‖ := by
      filter_upwards [hfreq] with r hr
      simpa [dist_zero_right] using hr
    set e : ℕ → EuclideanSpace ℝ (Fin (n i)) := fun r => (ε / ‖v r‖) • v r with he
    have hsph : ∀ᶠ r in (U : Filter ℕ), e r ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n i))) ε := by
      filter_upwards [hbig] with r hr
      have hpos : 0 < ‖v r‖ := hε.trans_le hr
      rw [mem_sphere_zero_iff_norm, he]
      simp only
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hε hpos), div_mul_cancel₀ _ hpos.ne']
    obtain ⟨eb, heb, hebt⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin (n i))) ε).ultrafilter_le_nhds
      (U.map e) (by rw [Ultrafilter.coe_map, le_principal_iff]; exact hsph)
    have het : Tendsto e (U : Filter ℕ) (𝓝 eb) := by
      rw [Ultrafilter.coe_map] at hebt; exact hebt
    -- the points on the segment
    have hseg : ∀ᶠ r in (U : Filter ℕ), x (g r) i + e r ∈ Xs i ∧
        u i (x (g r) i + e r) (x (g r)) ≤ f (x (g r)) := by
      filter_upwards [hbig, hgi] with r hr hri
      obtain ⟨h1, h2, -⟩ := bsum2a_run_step hx (g r) i hri
      have hy := hm (g r)
      have hy' := bsum2a_mem_Xset.1 hy
      have hcv := hqc i (x (g r)) hy (u i (x (g r) i) (x (g r)))
      have hpos : 0 < ‖v r‖ := hε.trans_le hr
      have hθ : ε / ‖v r‖ ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨(div_pos hε hpos).le, (div_le_one hpos).2 hr⟩
      have := hcv.add_smul_sub_mem ⟨hy' i, le_rfl⟩ ⟨h1, h2 _ (hy' i)⟩ hθ
      refine ⟨this.1, ?_⟩
      have h3 := this.2
      rw [hA2.B1 _ hy i] at h3
      exact h3
    have hpt : Tendsto (fun r => x (g r) i + e r) (U : Filter ℕ) (𝓝 (z i + eb)) :=
      hgi'.add het
    have hpmem : z i + eb ∈ Xs i :=
      (hXclosed i).mem_of_tendsto hpt (hseg.mono fun _ h => h.1)
    have hut := bsum2a_u_tendsto hA2 i hpt hg hpmem hzX (hseg.mono fun _ h => h.1)
      (Eventually.of_forall fun r => hm _)
    have hle1 : u i (z i + eb) z ≤ f z :=
      le_of_tendsto_of_tendsto hut hfx (hseg.mono fun _ h => h.2)
    have hge : ∀ w ∈ Xs i, f z ≤ u i w z := by
      intro w hw
      have hwt := bsum2a_u_tendsto hA2 i (tendsto_const_nhds (x := w)) hg hw hzX
        (Eventually.of_forall fun _ => hw) (Eventually.of_forall fun r => hm _)
      refine ge_of_tendsto hwt ?_
      filter_upwards [hgi] with r hri
      obtain ⟨-, h2, -⟩ := bsum2a_run_step hx (g r) i hri
      exact (hlow _).trans ((bsum2a_f_le_u hA2 hx (g r) i hri).trans (h2 w hw))
    obtain ⟨c0, -, huc⟩ := huniq i z hzX
    have e1 := huc (z i) ⟨hzX' i, fun w hw => by rw [hA2.B1 z hzX i]; exact hge w hw⟩
    have e2 := huc (z i + eb) ⟨hpmem, fun w hw => hle1.trans (hge w hw)⟩
    have : eb = 0 := by
      have h := e2.trans e1.symm
      simpa using h
    rw [mem_sphere_zero_iff_norm, this, norm_zero] at heb
    exact hε.ne heb
  rw [tendsto_pi_nhds]
  intro k
  by_cases hk : k = i
  · subst hk
    have hfun : (fun r => x (g r + 1) k) = fun r => x (g r) k + v r := by
      funext r; simp [hv]
    rw [hfun]
    simpa using hgi'.add hv0
  · have hgk : Tendsto (fun r => x (g r) k) (U : Filter ℕ) (𝓝 (z k)) :=
      ((continuous_apply k).tendsto z).comp hg
    exact hgk.congr' (hgi.mono fun r hr => ((bsum2a_run_step hx (g r) i hr).2.2 k hk).symm)

open BSUMConv.BSUM TsengBCD.Stationary Filter Topology in
theorem solution {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (hXconv : ∀ i, Convex ℝ (Xs i)) (hXclosed : ∀ i, IsClosed (Xs i))
    (f : X n → ℝ) (hf : ContinuousOn f (Xset Xs))
    (u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ) (hA2 : Assumption2 Xs f u)
    (hqc : BlockQuasiconvex Xs u) (huniq : ∀ i, UniqueBlockMin Xs u i)
    (s : ℕ → Fin N) (hs : IsCyclic s) (x : ℕ → X n) (hx : IsBSUMRun Xs u s x)
    (z : X n) (hz : MapClusterPt z atTop x) :
    IsCoordStationary Xs f z ∧
      (IsRegularAt (fext f (Xset Xs)) z → IsStationary (fext f (Xset Xs)) z) := by
  have hm := bsum2a_run_mem hx
  have hXc : IsClosed (Xset Xs) := isClosed_set_pi fun i _ => hXclosed i
  have hzX : z ∈ Xset Xs := hXc.mem_of_mapClusterPt hz (Eventually.of_forall hm)
  have hzX' := bsum2a_mem_Xset.1 hzX
  have hdesc : ∀ r, f (x (r + 1)) ≤ f (x r) := by
    intro r
    obtain ⟨-, h2, -⟩ := bsum2a_run_step hx r (s r) rfl
    have := (bsum2a_f_le_u hA2 hx r (s r) rfl).trans (h2 _ (bsum2a_mem_Xset.1 (hm r) (s r)))
    rwa [hA2.B1 _ (hm r)] at this
  have hanti : Antitone (fun r => f (x r)) := antitone_nat_of_succ_le hdesc
  have hlow : ∀ r, f z ≤ f (x r) := by
    intro r
    have hS : IsClosed (Xset Xs ∩ f ⁻¹' Set.Iic (f (x r))) :=
      hf.preimage_isClosed_of_isClosed hXc isClosed_Iic
    have := hS.mem_of_mapClusterPt hz
      ((eventually_ge_atTop r).mono fun r' hr' => ⟨hm r', hanti hr'⟩)
    exact this.2
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
    rw [hs, Nat.add_mod, ← hs r, hr]
    conv_rhs => rw [Nat.add_mod, Nat.mod_eq_of_lt a.isLt]
  have hconv : ∀ m : ℕ, Tendsto (fun r => x (r + m)) (U : Filter ℕ) (𝓝 z) := by
    intro m
    induction m with
    | zero => simpa using hUx
    | succ m ih =>
      have := bsum2a_step hXclosed hf hA2 hqc huniq hx hzX hlow U (fun r => r + m)
        ⟨((a : ℕ) + m) % N, Nat.mod_lt _ hNpos⟩
        ((hshift m).mono fun r hr => Fin.ext hr) ih
      simpa [add_assoc] using this
  have hcs : IsCoordStationary Xs f z := by
    refine ⟨hzX, fun k dk hk => ?_⟩
    set m : ℕ := N - (a : ℕ) + k with hmdef
    have hsk : ∀ᶠ r in (U : Filter ℕ), s (r + m) = k := by
      filter_upwards [hshift m] with r hr
      apply Fin.ext
      rw [hr, show (a : ℕ) + m = k + N by have := a.isLt; omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt k.isLt]
    have hmin : ∀ w ∈ Xs k, u k (z k) z ≤ u k w z := by
      intro w hw
      have hA : Tendsto (fun r => x (r + m + 1) k) (U : Filter ℕ) (𝓝 (z k)) :=
        ((continuous_apply k).tendsto z).comp (hconv (m + 1))
      have hl := bsum2a_u_tendsto hA2 k hA (hconv m) (hzX' k) hzX
        (hsk.mono fun r hr => (bsum2a_run_step hx (r + m) k hr).1)
        (Eventually.of_forall fun r => hm _)
      have hr := bsum2a_u_tendsto hA2 k (tendsto_const_nhds (x := w)) (hconv m) hw hzX
        (Eventually.of_forall fun _ => hw) (Eventually.of_forall fun r => hm _)
      exact le_of_tendsto_of_tendsto hl hr
        (hsk.mono fun r hr => (bsum2a_run_step hx (r + m) k hr).2.1 w hw)
    rw [← hA2.B3 z hzX k dk hk]
    unfold dirDeriv
    apply Filter.le_liminf_of_le (by isBoundedDefault)
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    have hmem : z k + t • dk ∈ Xs k :=
      (hXconv k).add_smul_mem (hzX' k) hk ⟨ht.1.le, ht.2.le⟩
    rw [← EReal.coe_sub, ← EReal.coe_mul]
    exact EReal.coe_nonneg.mpr (mul_nonneg (sub_nonneg.mpr (hmin _ hmem)) (inv_nonneg.mpr ht.1.le))
  refine ⟨hcs, fun hreg => ⟨hreg.1, fun d => hreg.2 d fun k => ?_⟩⟩
  by_cases hex : ∃ t0 : ℝ, 0 < t0 ∧ z k + t0 • d k ∈ Xs k
  · obtain ⟨t0, ht0, hmem⟩ := hex
    have h1 := hcs.2 k (t0 • d k) hmem
    rw [Pi.single_smul] at h1
    exact bsum2a_dirDeriv_nonneg_of_smul _ z _ ht0 h1
  · push_neg at hex
    unfold dirDeriv
    apply Filter.le_liminf_of_le (by isBoundedDefault)
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hnot : z + t • (Pi.single k (d k) : X n) ∉ Xset Xs := by
      intro h
      apply hex t ht
      have := bsum2a_mem_Xset.1 h k
      simpa using this
    rw [show fext f (Xset Xs) (z + t • (Pi.single k (d k) : X n)) = ⊤ from if_neg hnot,
      show fext f (Xset Xs) z = (f z : EReal) from if_pos hzX, EReal.top_sub_coe,
      EReal.top_mul_of_pos (by exact_mod_cast inv_pos.2 ht)]
    exact le_top
