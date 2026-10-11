-- Prove2me | solution 1 for FRBSplitting.Weak.theorem_2_5
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:03:22.43499+00:00
-- url     : https://prove2.me/submissions/cc43b474-7e11-4156-9a24-859ff7926bd1

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Weak_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace OpialKit

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Weak convergence, in the form every mission uses. -/
def WLim (x : ℕ → H) (p : H) : Prop :=
  ∀ v : H, Tendsto (fun n => inner ℝ (x n) v) atTop (𝓝 (inner ℝ p v))

/-- K1. Bounded sequences in a real Hilbert space have weakly convergent subsequences. -/
theorem exists_wlim_subseq [CompleteSpace H] (x : ℕ → H) (C : ℝ) (hC : ∀ n, ‖x n‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p : H, WLim (x ∘ φ) p := by
  set M : Submodule ℝ H := (Submodule.span ℝ (Set.range x)).topologicalClosure with hMdef
  have hMc : IsClosed (M : Set H) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace M := hMc.completeSpace_coe
  have hsep : TopologicalSpace.IsSeparable (M : Set H) := by
    rw [hMdef, Submodule.topologicalClosure_coe]
    exact (Set.countable_range x).isSeparable.span.closure
  have : TopologicalSpace.SeparableSpace M := hsep.separableSpace
  have hmem : ∀ n, x n ∈ M := fun n =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)
  let y : ℕ → M := fun n => ⟨x n, hmem n⟩
  let u : ℕ → WeakDual ℝ M := fun n => StrongDual.toWeakDual (innerSL ℝ (y n))
  have hu : ∀ n, u n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ M) C := by
    intro n
    change dist (innerSL ℝ (y n)) 0 ≤ C
    rw [dist_zero_right, innerSL_apply_norm]
    exact hC n
  obtain ⟨a, -, φ, hφ, hlim⟩ := WeakDual.isSeqCompact_closedBall ℝ M 0 C hu
  refine ⟨φ, hφ, ((InnerProductSpace.toDual ℝ M).symm (WeakDual.toStrongDual a) : H), ?_⟩
  intro v
  have h1 : ∀ n, inner ℝ ((x ∘ φ) n) v = (u (φ n)) (M.orthogonalProjectionOnto v) := by
    intro n
    simp only [Function.comp, u]
    rw [← Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (y (φ n)) v]
    rfl
  have h2 : inner ℝ (((InnerProductSpace.toDual ℝ M).symm (WeakDual.toStrongDual a) : M) : H) v
      = a (M.orthogonalProjectionOnto v) := by
    rw [← Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, InnerProductSpace.toDual_symm_apply]
    rfl
  simp_rw [h1, h2]
  exact ((WeakDual.eval_continuous (M.orthogonalProjectionOnto v)).tendsto a).comp hlim

/-- K2. Weak limits are unique. -/
theorem wlim_unique {x : ℕ → H} {p q : H} (hp : WLim x p) (hq : WLim x q) : p = q := by
  have h : inner ℝ p (p - q) = inner ℝ q (p - q) := tendsto_nhds_unique (hp (p - q)) (hq (p - q))
  have h2 : inner ℝ (p - q) (p - q) = 0 := by rw [inner_sub_left, h, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h2)


/-- K2'. A weak limit of a subsequence is a weak limit of further subsequences. -/
theorem wlim_comp {x : ℕ → H} {p : H} (hp : WLim x p) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    WLim (x ∘ φ) p := fun v => (hp v).comp hφ.tendsto_atTop

private theorem aux_cluster_unique {x : ℕ → H} {p q : H}
    (hp : ∃ r : ℝ, Tendsto (fun n => ‖x n - p‖) atTop (𝓝 r))
    (hq : ∃ r : ℝ, Tendsto (fun n => ‖x n - q‖) atTop (𝓝 r))
    {φ ψ : ℕ → ℕ} (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (h1 : WLim (x ∘ φ) p) (h2 : WLim (x ∘ ψ) q) : p = q := by
  obtain ⟨rp, hrp⟩ := hp
  obtain ⟨rq, hrq⟩ := hq
  have hid : ∀ n, inner ℝ (x n) (q - p)
      = ((‖x n - p‖ ^ 2 - ‖x n - q‖ ^ 2) - ‖p‖ ^ 2 + ‖q‖ ^ 2) / 2 := by
    intro n
    rw [norm_sub_sq_real, norm_sub_sq_real, inner_sub_right]
    ring
  have hg : Tendsto (fun n => inner ℝ (x n) (q - p)) atTop
      (𝓝 (((rp ^ 2 - rq ^ 2) - ‖p‖ ^ 2 + ‖q‖ ^ 2) / 2)) := by
    simp_rw [hid]
    exact ((((hrp.pow 2).sub (hrq.pow 2)).sub_const _).add_const _).div_const _
  have e1 := tendsto_nhds_unique (hg.comp hφ.tendsto_atTop) (h1 (q - p))
  have e2 := tendsto_nhds_unique (hg.comp hψ.tendsto_atTop) (h2 (q - p))
  have h0 : inner ℝ (q - p) (q - p) = 0 := by rw [inner_sub_left, ← e1, ← e2, sub_self]
  exact (sub_eq_zero.mp (inner_self_eq_zero.mp h0)).symm

/-- K3. Opial's lemma. If `‖x n - z‖` converges for every `z ∈ S` and every weak sequential
cluster point of `x` lies in `S`, then `x` converges weakly to a point of `S`. -/
theorem opial [CompleteSpace H] (S : Set H) (hS : S.Nonempty) (x : ℕ → H)
    (hfej : ∀ z ∈ S, ∃ r : ℝ, Tendsto (fun n => ‖x n - z‖) atTop (𝓝 r))
    (hclu : ∀ (φ : ℕ → ℕ) (p : H), StrictMono φ → WLim (x ∘ φ) p → p ∈ S) :
    ∃ p ∈ S, WLim x p := by
  obtain ⟨z0, hz0⟩ := hS
  obtain ⟨r0, hr0⟩ := hfej z0 hz0
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ hr0)
  have hbd : ∀ n, ‖x n‖ ≤ B + ‖z0‖ := by
    intro n
    have h := hB _ ⟨n, rfl⟩
    rw [Real.norm_of_nonneg (norm_nonneg _)] at h
    calc ‖x n‖ = ‖(x n - z0) + z0‖ := by rw [sub_add_cancel]
      _ ≤ ‖x n - z0‖ + ‖z0‖ := norm_add_le _ _
      _ ≤ B + ‖z0‖ := by linarith
  obtain ⟨φ, hφ, p, hp⟩ := exists_wlim_subseq x _ hbd
  have hpS := hclu φ p hφ hp
  refine ⟨p, hpS, fun v => ?_⟩
  by_contra hne
  obtain ⟨s, hs, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.mp hne
  obtain ⟨ψ, hψ, hout⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨χ, hχ, q, hq⟩ := exists_wlim_subseq (x ∘ ψ) _ (fun n => hbd (ψ n))
  have hqS := hclu (ψ ∘ χ) q (hψ.comp hχ) hq
  have hpq : p = q := aux_cluster_unique (hfej p hpS) (hfej q hqS) hφ (hψ.comp hχ) hp hq
  have ht := hq v
  rw [← hpq] at ht
  obtain ⟨n, hn⟩ := (ht.eventually hs).exists
  exact hout (χ n) hn

/-- Monotone set-valued operator, as a relation. -/
def Mono (T : H → Set H) : Prop :=
  ∀ x y u v, u ∈ T x → v ∈ T y → 0 ≤ inner ℝ (x - y) (u - v)

/-- Maximal monotone, in the "no proper monotone extension" form the missions use. -/
def MaxMono (T : H → Set H) : Prop :=
  Mono T ∧ ∀ T' : H → Set H, Mono T' → (∀ x, T x ⊆ T' x) → T' = T

/-- K4a. A point monotonically related to the graph of a maximal monotone operator is in it. -/
theorem MaxMono.mem_of_related {T : H → Set H} (hT : MaxMono T) {x u : H}
    (h : ∀ y v, v ∈ T y → 0 ≤ inner ℝ (x - y) (u - v)) : u ∈ T x := by
  let T' : H → Set H := fun z => {w | w ∈ T z ∨ (z = x ∧ w = u)}
  have hmono : Mono T' := by
    intro a b c d hc hd
    rcases hc with hc | ⟨rfl, rfl⟩ <;> rcases hd with hd | ⟨rfl, rfl⟩
    · exact hT.1 _ _ _ _ hc hd
    · have := h a c hc
      have e : inner ℝ (a - b) (c - d) = inner ℝ (b - a) (d - c) := by
        rw [← neg_sub b a, ← neg_sub d c, inner_neg_neg]
      rw [e]; exact this
    · exact h b d hd
    · simp
  have hsub : ∀ z, T z ⊆ T' z := fun z w hw => Or.inl hw
  have hEq := hT.2 T' hmono hsub
  have : u ∈ T' x := Or.inr ⟨rfl, rfl⟩
  rw [hEq] at this
  exact this


private theorem aux_bdd_of_wlim [CompleteSpace H] {x : ℕ → H} {p : H} (hx : WLim x p) :
    ∃ C, ∀ n, ‖x n‖ ≤ C := by
  have hpt : ∀ v : H, ∃ C, ∀ n, ‖(innerSL ℝ (x n)) v‖ ≤ C := by
    intro v
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
      (Metric.isBounded_range_of_tendsto _ (hx v))
    exact ⟨C, fun n => by rw [innerSL_apply_apply]; exact hC _ ⟨n, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hpt
  exact ⟨C, fun n => by rw [← innerSL_apply_norm ℝ (x n)]; exact hC n⟩

/-- K4b under `CompleteSpace H` (the frozen K4b omits it; see KIT.md). -/
theorem aux_demiclosed_of_complete [CompleteSpace H] {T : H → Set H} (hT : MaxMono T)
    {x u : ℕ → H} {p q : H}
    (hmem : ∀ n, u n ∈ T (x n)) (hx : WLim x p) (hu : Tendsto u atTop (𝓝 q)) : q ∈ T p := by
  obtain ⟨C, hC⟩ := aux_bdd_of_wlim hx
  apply hT.mem_of_related
  intro y v hv
  have key : ∀ n, inner ℝ (x n - y) (u n - v)
      = (inner ℝ (x n) (q - v) - inner ℝ y (q - v)) + inner ℝ (x n - y) (u n - q) := by
    intro n
    rw [← inner_sub_left, ← inner_add_right]; congr 1; abel
  have h1 : Tendsto (fun n => inner ℝ (x n) (q - v) - inner ℝ y (q - v)) atTop
      (𝓝 (inner ℝ p (q - v) - inner ℝ y (q - v))) := (hx (q - v)).sub tendsto_const_nhds
  have h2 : Tendsto (fun n => inner ℝ (x n - y) (u n - q)) atTop (𝓝 0) := by
    have hq : Tendsto (fun n => (C + ‖y‖) * ‖u n - q‖) atTop (𝓝 0) := by
      have : Tendsto (fun n => ‖u n - q‖) atTop (𝓝 0) := by
        have := (hu.sub_const q).norm
        simpa using this
      simpa using this.const_mul (C + ‖y‖)
    refine squeeze_zero_norm (fun n => ?_) hq
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    gcongr
    exact (norm_sub_le _ _).trans (by linarith [hC n])
  have hlim := h1.add h2
  rw [add_zero, ← inner_sub_left] at hlim
  have hlim' : Tendsto (fun n => inner ℝ (x n - y) (u n - v)) atTop
      (𝓝 (inner ℝ (p - y) (q - v))) := by
    simp_rw [key]; exact hlim
  exact ge_of_tendsto' hlim' (fun n => hT.1 _ _ _ _ (hmem n) hv)

/-- K4b. Demiclosedness: the graph of a maximal monotone operator is weak × strong
sequentially closed (in a Hilbert space; false without completeness). -/
theorem MaxMono.demiclosed [CompleteSpace H] {T : H → Set H} (hT : MaxMono T) {x u : ℕ → H} {p q : H}
    (hmem : ∀ n, u n ∈ T (x n)) (hx : WLim x p) (hu : Tendsto u atTop (𝓝 q)) : q ∈ T p :=
  aux_demiclosed_of_complete hT hmem hx hu

private theorem aux_mem_of_related_surj {T : H → Set H} {μ : ℝ} (hμ : 0 < μ)
    (hsurj : ∀ z : H, ∃ x u, u ∈ T x ∧ z = x + μ • u) {x u : H}
    (h : ∀ y v, v ∈ T y → 0 ≤ inner ℝ (x - y) (u - v)) : u ∈ T x := by
  obtain ⟨y, w, hw, hz⟩ := hsurj (x + μ • u)
  have hxy : x - y = μ • (w - u) := by
    rw [smul_sub]
    calc x - y = (x + μ • u) - y - μ • u := by abel
      _ = (y + μ • w) - y - μ • u := by rw [hz]
      _ = μ • w - μ • u := by abel
  have h0 := h y w hw
  rw [hxy, inner_smul_left, ← neg_sub w u, inner_neg_right, real_inner_self_eq_norm_sq] at h0
  simp only [RCLike.conj_to_real] at h0
  have hn : ‖w - u‖ ^ 2 ≤ 0 := by nlinarith
  have hwu : w - u = 0 := by
    have : ‖w - u‖ = 0 := by nlinarith [norm_nonneg (w - u)]
    exact norm_eq_zero.mp this
  have hwu' : w = u := sub_eq_zero.mp hwu
  have hxy' : x = y := by rw [← sub_eq_zero, hxy, hwu, smul_zero]
  rw [hxy', ← hwu']; exact hw

/-- K5. Easy direction of Minty: a monotone operator with `range (I + μT) = H` for one `μ > 0`
is maximal monotone. -/
theorem maxMono_of_surj {T : H → Set H} (hT : Mono T) {μ : ℝ} (hμ : 0 < μ)
    (hsurj : ∀ z : H, ∃ x u, u ∈ T x ∧ z = x + μ • u) : MaxMono T := by
  refine ⟨hT, fun T' hT' hsub => ?_⟩
  funext z
  apply Set.Subset.antisymm _ (hsub z)
  intro w hw
  exact aux_mem_of_related_surj hμ hsurj
    (fun y v hv => hT' _ _ _ _ hw (hsub y hv))


private theorem aux_le_of_sq_le {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ a * b) :
    a ≤ b := by nlinarith

private theorem aux_resolvent_nonexp {A : H → Set H} (hA : Mono A) {J : H → H} {μ : ℝ}
    (hμ : 0 < μ) (hJ : ∀ z, μ⁻¹ • (z - J z) ∈ A (J z)) (w1 w2 : H) :
    ‖J w1 - J w2‖ ≤ ‖w1 - w2‖ := by
  have h := hA _ _ _ _ (hJ w1) (hJ w2)
  have e : μ⁻¹ • (w1 - J w1) - μ⁻¹ • (w2 - J w2) = μ⁻¹ • ((w1 - w2) - (J w1 - J w2)) := by
    rw [← smul_sub]; congr 1; abel
  rw [e, inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq] at h
  have hμ' : 0 < μ⁻¹ := inv_pos.mpr hμ
  have h' : 0 ≤ inner ℝ (J w1 - J w2) (w1 - w2) - ‖J w1 - J w2‖ ^ 2 :=
    nonneg_of_mul_nonneg_right (by linarith) hμ'
  have hc := real_inner_le_norm (J w1 - J w2) (w1 - w2)
  exact aux_le_of_sq_le (norm_nonneg _) (norm_nonneg _) (by linarith)

/-- K6. If `A` is maximal monotone with resolvents `J γ` (in the missions' `IsResolvent` form) and
`B` is monotone and `L`-Lipschitz, then `A + B` is maximal monotone. -/
theorem maxMono_add_lipschitz [CompleteSpace H] {A : H → Set H} (hA : MaxMono A)
    (J : ℝ → H → H) (hJ : ∀ γ : ℝ, 0 < γ → ∀ z, γ⁻¹ • (z - J γ z) ∈ A (J γ z))
    {B : H → H} (hBm : ∀ x y, 0 ≤ inner ℝ (x - y) (B x - B y))
    {L : ℝ} (hL : 0 < L) (hBL : ∀ x y, ‖B x - B y‖ ≤ L * ‖x - y‖) :
    MaxMono (fun x => {w | ∃ a ∈ A x, w = a + B x}) := by
  have hmono : Mono (fun x => {w | ∃ a ∈ A x, w = a + B x}) := by
    rintro x y _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    have e : a + B x - (b + B y) = (a - b) + (B x - B y) := by abel
    rw [e, inner_add_right]
    exact add_nonneg (hA.1 _ _ _ _ ha hb) (hBm x y)
  set μ : ℝ := (2 * L)⁻¹ with hμdef
  have hμ : 0 < μ := by positivity
  have hμL : μ * L = 1 / 2 := by rw [hμdef]; field_simp
  refine maxMono_of_surj hmono hμ ?_
  intro z
  let F : H → H := fun y => J μ (z - μ • B y)
  have hF : ContractingWith (1 / 2 : NNReal) F := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun y1 y2 => ?_⟩
    rw [dist_eq_norm, dist_eq_norm]
    refine (aux_resolvent_nonexp hA.1 hμ (hJ μ hμ) _ _).trans ?_
    have e : z - μ • B y1 - (z - μ • B y2) = -(μ • (B y1 - B y2)) := by
      rw [smul_sub]; abel
    rw [e, norm_neg, norm_smul, Real.norm_of_nonneg hμ.le]
    have := hBL y1 y2
    have h2 : μ * ‖B y1 - B y2‖ ≤ μ * (L * ‖y1 - y2‖) := mul_le_mul_of_nonneg_left this hμ.le
    calc μ * ‖B y1 - B y2‖ ≤ μ * (L * ‖y1 - y2‖) := h2
      _ = (μ * L) * ‖y1 - y2‖ := by ring
      _ = ((1 / 2 : NNReal) : ℝ) * ‖y1 - y2‖ := by rw [hμL]; norm_num
  set y := ContractingWith.fixedPoint F hF
  have hy : F y = y := ContractingWith.fixedPoint_isFixedPt (f := F) hF
  set w := z - μ • B y
  refine ⟨y, μ⁻¹ • (w - J μ w) + B y, ⟨μ⁻¹ • (w - J μ w), ?_, rfl⟩, ?_⟩
  · have := hJ μ hμ w
    have hFy : J μ w = y := hy
    rw [hFy] at this ⊢
    exact this
  · have hFy : J μ w = y := hy
    rw [hFy, smul_add, smul_smul, mul_inv_cancel₀ hμ.ne', one_smul]
    simp only [w]; abel

end OpialKit

namespace RRAux_FRBSplitting_Weak_theorem_2_5

open Filter Topology

theorem step_real (nb nc D0 D1 l0 l1 L ε P Q R M : ℝ)
    (h : 0 ≤ (nb ^ 2 - nc ^ 2 - D1 ^ 2) / 2 - l1 * (M - P) - l0 * (Q + R))
    (hM : 0 ≤ M) (hl1 : 0 ≤ l1) (hl0 : 0 ≤ l0) (hL : 0 < L)
    (hR : -(L * (D1 * D0)) ≤ R) (hD0 : 0 ≤ D0) (hD1 : 0 ≤ D1)
    (hl0L : l0 * L ≤ (1 - 2 * ε) / 2) :
    nc ^ 2 / 2 - l1 * P + (1 - 2 * ε) / 4 * D1 ^ 2
      ≤ nb ^ 2 / 2 - l0 * Q + (1 - 2 * ε) / 4 * D0 ^ 2 - ε * D1 ^ 2 := by
  have h1 : -(l0 * R) ≤ l0 * L * (D1 * D0) := by nlinarith [mul_le_mul_of_nonneg_left hR hl0]
  have h2 : l0 * L * (D1 * D0) ≤ (1 - 2 * ε) / 2 * (D1 * D0) :=
    mul_le_mul_of_nonneg_right hl0L (mul_nonneg hD1 hD0)
  have hε : 0 ≤ 1 - 2 * ε := by nlinarith [mul_nonneg hl0 hL.le]
  have h3 : (1 - 2 * ε) / 2 * (D1 * D0) ≤ (1 - 2 * ε) / 4 * (D1 ^ 2 + D0 ^ 2) := by
    nlinarith [mul_nonneg hε (sq_nonneg (D1 - D0))]
  have h4 : 0 ≤ l1 * M := mul_nonneg hl1 hM
  nlinarith

theorem lower_real (nb D0 l0 L ε Q : ℝ) (hl0 : 0 ≤ l0) (hL : 0 < L) (hε : 0 ≤ ε)
    (hQ : Q ≤ L * (nb * D0)) (hnb : 0 ≤ nb) (hD0 : 0 ≤ D0)
    (hl0L : l0 * L ≤ (1 - 2 * ε) / 2) :
    nb ^ 2 / 4 ≤ nb ^ 2 / 2 - l0 * Q + (1 - 2 * ε) / 4 * D0 ^ 2 := by
  have h1 : l0 * Q ≤ l0 * L * (nb * D0) := by nlinarith [mul_le_mul_of_nonneg_left hQ hl0]
  have h2 : l0 * L * (nb * D0) ≤ (1 - 2 * ε) / 2 * (nb * D0) :=
    mul_le_mul_of_nonneg_right hl0L (mul_nonneg hnb hD0)
  have hε' : 0 ≤ 1 - 2 * ε := by nlinarith [mul_nonneg hl0 hL.le]
  have h3 : (1 - 2 * ε) / 2 * (nb * D0) ≤ (1 - 2 * ε) / 4 * (nb ^ 2 + D0 ^ 2) := by
    nlinarith [mul_nonneg hε' (sq_nonneg (nb - D0))]
  nlinarith [mul_nonneg hε (sq_nonneg nb)]

theorem sq_bound (t M : ℝ) (_ht : 0 ≤ t) (h : t ^ 2 ≤ M) : t ≤ 1 + M := by
  nlinarith [sq_nonneg (t - 1)]

theorem lamL (l L ε : ℝ) (hL : 0 < L) (h : l ≤ (1 - 2 * ε) / (2 * L)) :
    l * L ≤ (1 - 2 * ε) / 2 := by
  rw [le_div_iff₀ (by positivity)] at h
  linarith

section Vec
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem vec_ineq (b c z ga gb gc gz : H) (l0 l1 : ℝ)
    (h : 0 ≤ inner ℝ (c - z) ((b - c) - l1 • (gb - gz) - l0 • (gb - ga))) :
    0 ≤ (‖b - z‖ ^ 2 - ‖c - z‖ ^ 2 - ‖c - b‖ ^ 2) / 2
      - l1 * (inner ℝ (c - z) (gc - gz) - inner ℝ (c - z) (gc - gb))
      - l0 * (inner ℝ (b - z) (gb - ga) + inner ℝ (c - b) (gb - ga)) := by
  have e1 : inner ℝ (c - z) ((b - c) - l1 • (gb - gz) - l0 • (gb - ga))
      = inner ℝ (c - z) (b - c) - l1 * inner ℝ (c - z) (gb - gz)
        - l0 * inner ℝ (c - z) (gb - ga) := by
    rw [inner_sub_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right]
  have e2 : inner ℝ (c - z) (gb - gz)
      = inner ℝ (c - z) (gc - gz) - inner ℝ (c - z) (gc - gb) := by
    rw [← inner_sub_right]; congr 1; abel
  have e3 : inner ℝ (c - z) (gb - ga)
      = inner ℝ (b - z) (gb - ga) + inner ℝ (c - b) (gb - ga) := by
    rw [← inner_add_left]; congr 1; abel
  have e4 : ‖b - z‖ ^ 2 = ‖c - b‖ ^ 2 + 2 * inner ℝ (c - z) (b - c) + ‖c - z‖ ^ 2 := by
    have : b - z = (b - c) + (c - z) := by abel
    rw [this, norm_add_sq_real, norm_sub_rev b c, real_inner_comm (c - z) (b - c)]
  rw [e1, e2, e3] at h
  linarith

theorem resolvent_ineq (b c z ga gb gz : H) (l0 l1 : ℝ) (hl1 : 0 < l1)
    (h : 0 ≤ inner ℝ (c - z) (l1⁻¹ • ((b - l1 • gb - l0 • (gb - ga)) - c) - -gz)) :
    0 ≤ inner ℝ (c - z) ((b - c) - l1 • (gb - gz) - l0 • (gb - ga)) := by
  have : (b - c) - l1 • (gb - gz) - l0 • (gb - ga)
      = l1 • (l1⁻¹ • ((b - l1 • gb - l0 • (gb - ga)) - c) - -gz) := by
    rw [smul_sub l1 (l1⁻¹ • _) (-gz), smul_smul, mul_inv_cancel₀ hl1.ne', one_smul]; module
  rw [this, real_inner_smul_right]; exact mul_nonneg hl1.le h

theorem U_eq (b c ga gb gc : H) (l0 l1 : ℝ) (hl1 : l1 ≠ 0) :
    l1⁻¹ • ((b - l1 • gb - l0 • (gb - ga)) - c) + gc
      = l1⁻¹ • (b - c) + (gc - gb) - (l1⁻¹ * l0) • (gb - ga) := by
  have : l1⁻¹ • (l1 • gb) = gb := by rw [smul_smul, inv_mul_cancel₀ hl1, one_smul]
  simp only [smul_sub, mul_smul, this]; abel

theorem U_bound (b c a ga gb gc : H) (l1 l0 ε Λ L : ℝ) (hε : 0 < ε) (h1 : ε ≤ l1)
    (h0 : 0 ≤ l0) (h0' : l0 ≤ Λ) (hgc : ‖gc - gb‖ ≤ L * ‖c - b‖)
    (hgb : ‖gb - ga‖ ≤ L * ‖b - a‖) :
    ‖l1⁻¹ • (b - c) + (gc - gb) - (l1⁻¹ * l0) • (gb - ga)‖
      ≤ ε⁻¹ * ‖c - b‖ + L * ‖c - b‖ + (ε⁻¹ * Λ) * (L * ‖b - a‖) := by
  have hl1 : 0 < l1 := lt_of_lt_of_le hε h1
  have i1 : l1⁻¹ ≤ ε⁻¹ := inv_anti₀ hε h1
  have n1 : ‖l1⁻¹ • (b - c)‖ ≤ ε⁻¹ * ‖c - b‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hl1.le), norm_sub_rev]
    exact mul_le_mul_of_nonneg_right i1 (norm_nonneg _)
  have hΛ : 0 ≤ Λ := h0.trans h0'
  have hL : 0 ≤ L * ‖b - a‖ := (norm_nonneg _).trans hgb
  have n3 : ‖(l1⁻¹ * l0) • (gb - ga)‖ ≤ (ε⁻¹ * Λ) * (L * ‖b - a‖) := by
    rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hl1.le) h0)]
    exact mul_le_mul (mul_le_mul i1 h0' h0 (inv_nonneg.2 hε.le)) hgb (norm_nonneg _)
      (mul_nonneg (inv_nonneg.2 hε.le) hΛ)
  have n4 := norm_sub_le (l1⁻¹ • (b - c) + (gc - gb)) ((l1⁻¹ * l0) • (gb - ga))
  have n5 := norm_add_le (l1⁻¹ • (b - c)) (gc - gb)
  linarith

theorem wlim_shift (y w : ℕ → H) (p : H) (hy : OpialKit.WLim y p)
    (hd : Tendsto (fun k => ‖w k - y k‖) atTop (𝓝 0)) : OpialKit.WLim w p := by
  intro v
  have h1 : Tendsto (fun k => inner ℝ (w k - y k) v) atTop (𝓝 0) :=
    squeeze_zero_norm (a := fun k => ‖w k - y k‖ * ‖v‖)
      (fun k => by rw [Real.norm_eq_abs]; exact abs_real_inner_le_norm _ _)
      (by simpa using hd.mul_const ‖v‖)
  have := (hy v).add h1
  simp only [add_zero] at this
  refine this.congr (fun k => ?_)
  rw [inner_sub_left]; ring

end Vec

theorem real_conv (F d e : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hstep : ∀ k, F (k + 1) ≤ F k - ε * d (k + 1) ^ 2) (hlow : ∀ k, e k ^ 2 / 4 ≤ F k)
    (hd : ∀ k, 0 ≤ d k) (he : ∀ k, 0 ≤ e k) :
    (∃ Fl, Tendsto F atTop (𝓝 Fl)) ∧ Tendsto d atTop (𝓝 0) ∧ ∀ k, e k ≤ 1 + 4 * F 0 := by
  have anti : Antitone F := antitone_nat_of_succ_le (fun k => by
    have := mul_nonneg hε.le (sq_nonneg (d (k + 1)))
    linarith [hstep k])
  have bdd : BddBelow (Set.range F) := ⟨0, by
    rintro _ ⟨k, rfl⟩
    have := sq_nonneg (e k)
    linarith [hlow k]⟩
  have hF := tendsto_atTop_ciInf anti bdd
  refine ⟨⟨_, hF⟩, ?_, ?_⟩
  · have h2 : Tendsto (fun k => F (k + 1)) atTop (𝓝 (⨅ i, F i)) :=
      (tendsto_add_atTop_iff_nat 1).mpr hF
    have hdiff := hF.sub h2
    rw [sub_self] at hdiff
    have hsq : Tendsto (fun k => d (k + 1) ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero (fun k => sq_nonneg _) (fun k => ?_) (g := fun k => (F k - F (k + 1)) / ε)
        (by simpa using hdiff.div_const ε)
      rw [le_div_iff₀ hε]; nlinarith [hstep k]
    have h3 := (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at h3
    have h4 : (Real.sqrt ∘ fun k => d (k + 1) ^ 2) = fun k => d (k + 1) :=
      funext fun k => Real.sqrt_sq (hd _)
    rw [h4] at h3
    exact (tendsto_add_atTop_iff_nat 1).mp h3
  · intro k
    apply sq_bound _ _ (he k)
    have := anti (Nat.zero_le k)
    linarith [hlow k]

theorem norm_conv (F d e Q lamk : ℕ → ℝ) (ε Λ C Fl : ℝ)
    (hF : Tendsto F atTop (𝓝 Fl)) (hd : Tendsto d atTop (𝓝 0))
    (hdef : ∀ k, F k = e k ^ 2 / 2 - lamk k * Q k + (1 - 2 * ε) / 4 * d k ^ 2)
    (hQ : ∀ k, |Q k| ≤ C * d k) (hlam : ∀ k, |lamk k| ≤ Λ) (he : ∀ k, 0 ≤ e k) :
    ∃ r, Tendsto e atTop (𝓝 r) := by
  have h1 : Tendsto (fun k => lamk k * Q k) atTop (𝓝 0) :=
    squeeze_zero_norm (a := fun k => Λ * (C * d k)) (fun k => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hlam k) (hQ k) (abs_nonneg _) ((abs_nonneg _).trans (hlam k)))
      (by simpa using (hd.const_mul C).const_mul Λ)
  have h2 := ((hF.add h1).sub ((hd.pow 2).const_mul ((1 - 2 * ε) / 4))).const_mul 2
  have h3 : (fun k => 2 * (F k + lamk k * Q k - (1 - 2 * ε) / 4 * d k ^ 2))
      = fun k => e k ^ 2 := funext fun k => by rw [hdef k]; ring
  rw [h3] at h2
  refine ⟨Real.sqrt (2 * (Fl + 0 - (1 - 2 * ε) / 4 * 0 ^ 2)), ?_⟩
  have h4 := (Real.continuous_sqrt.tendsto _).comp h2
  have h5 : (Real.sqrt ∘ fun k => e k ^ 2) = e := funext fun k => Real.sqrt_sq (he k)
  rw [h5] at h4
  exact h4

section Main
open ThreeOpSplitting.Accel FRBSplitting.Weak
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

noncomputable def Fn (B : H → H) (lam : ℕ → ℝ) (x : ℕ → H) (ε : ℝ) (z : H) (k : ℕ) : ℝ :=
  ‖x (k + 1) - z‖ ^ 2 / 2 - lam k * inner ℝ (x (k + 1) - z) (B (x (k + 1)) - B (x k))
    + (1 - 2 * ε) / 4 * ‖x (k + 1) - x k‖ ^ 2

noncomputable def Uop (B : H → H) (lam : ℕ → ℝ) (x : ℕ → H) (n : ℕ) : H :=
  (lam (n + 1))⁻¹ • ((x (n + 1) - lam (n + 1) • B (x (n + 1)) - lam n • (B (x (n + 1)) - B (x n)))
    - x (n + 2)) + B (x (n + 2))

theorem Fn_step (A : H → Set H) (B : H → H) (J : ℝ → H → H) (L ε : ℝ)
    (hA : IsMaximalMonotone A) (hJ : IsResolventFamily A J) (hBm : IsMonotoneFun B)
    (hL : 0 < L) (hBL : IsLipschitzOp L B) (hε : 0 < ε) (lam : ℕ → ℝ)
    (hlam : ∀ j, ε ≤ lam j ∧ lam j ≤ (1 - 2 * ε) / (2 * L))
    (x : ℕ → H) (hrun : IsFRBRun J B lam x) (z : H) (hz : -B z ∈ A z) (k : ℕ) :
    Fn B lam x ε z (k + 1) ≤ Fn B lam x ε z k - ε * ‖x (k + 1 + 1) - x (k + 1)‖ ^ 2 := by
  obtain ⟨hAm, -⟩ := hA
  have hl1 : 0 < lam (k + 1) := lt_of_lt_of_le hε (hlam (k + 1)).1
  have hl0 : 0 ≤ lam k := hε.le.trans (hlam k).1
  have hl0L := lamL _ _ _ hL (hlam k).2
  have hres := hJ (lam (k + 1)) hl1
    (x (k + 1) - lam (k + 1) • B (x (k + 1)) - lam k • (B (x (k + 1)) - B (x k)))
  rw [← hrun k] at hres
  have hmono := hAm _ _ _ _ hres hz
  have h1 := vec_ineq (x (k + 1)) (x (k + 2)) z (B (x k)) (B (x (k + 1))) (B (x (k + 2))) (B z)
    (lam k) (lam (k + 1))
    (resolvent_ineq (x (k + 1)) (x (k + 2)) z (B (x k)) (B (x (k + 1))) (B z) (lam k) (lam (k + 1))
      hl1 hmono)
  have hM := hBm (x (k + 2)) z
  have hR : -(L * (‖x (k + 2) - x (k + 1)‖ * ‖x (k + 1) - x k‖))
      ≤ inner ℝ (x (k + 2) - x (k + 1)) (B (x (k + 1)) - B (x k)) := by
    have a1 := abs_real_inner_le_norm (x (k + 2) - x (k + 1)) (B (x (k + 1)) - B (x k))
    have a2 := mul_le_mul_of_nonneg_left (hBL (x (k + 1)) (x k))
      (norm_nonneg (x (k + 2) - x (k + 1)))
    have a3 := neg_abs_le (inner ℝ (x (k + 2) - x (k + 1)) (B (x (k + 1)) - B (x k)))
    linarith
  have := step_real _ _ _ _ _ _ _ _ _ _ _ _ h1 hM hl1.le hl0 hL hR (norm_nonneg _)
    (norm_nonneg _) hl0L
  unfold Fn
  exact this

theorem Fn_lower (B : H → H) (L ε : ℝ) (hL : 0 < L) (hBL : IsLipschitzOp L B) (hε : 0 < ε)
    (lam : ℕ → ℝ) (hlam : ∀ j, ε ≤ lam j ∧ lam j ≤ (1 - 2 * ε) / (2 * L))
    (x : ℕ → H) (z : H) (k : ℕ) :
    ‖x (k + 1) - z‖ ^ 2 / 4 ≤ Fn B lam x ε z k := by
  have hl0 : 0 ≤ lam k := hε.le.trans (hlam k).1
  have hl0L := lamL _ _ _ hL (hlam k).2
  unfold Fn
  apply lower_real _ _ _ _ _ _ hl0 hL hε.le _ (norm_nonneg _) (norm_nonneg _) hl0L
  have a1 := real_inner_le_norm (x (k + 1) - z) (B (x (k + 1)) - B (x k))
  have a2 := mul_le_mul_of_nonneg_left (hBL (x (k + 1)) (x k)) (norm_nonneg (x (k + 1) - z))
  linarith

theorem fejer (A : H → Set H) (B : H → H) (J : ℝ → H → H) (L ε : ℝ)
    (hA : IsMaximalMonotone A) (hJ : IsResolventFamily A J) (hBm : IsMonotoneFun B)
    (hL : 0 < L) (hBL : IsLipschitzOp L B) (hε : 0 < ε) (lam : ℕ → ℝ)
    (hlam : ∀ j, ε ≤ lam j ∧ lam j ≤ (1 - 2 * ε) / (2 * L))
    (x : ℕ → H) (hrun : IsFRBRun J B lam x) (z : H) (hz : -B z ∈ A z) :
    (∃ r, Tendsto (fun n => ‖x n - z‖) atTop (𝓝 r))
      ∧ Tendsto (fun n => ‖x (n + 1) - x n‖) atTop (𝓝 0) := by
  obtain ⟨⟨Fl, hF⟩, hd, hb⟩ := real_conv (Fn B lam x ε z) (fun n => ‖x (n + 1) - x n‖)
    (fun n => ‖x (n + 1) - z‖) ε hε
    (fun k => Fn_step A B J L ε hA hJ hBm hL hBL hε lam hlam x hrun z hz k)
    (fun k => Fn_lower B L ε hL hBL hε lam hlam x z k) (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _)
  refine ⟨?_, hd⟩
  have hQ : ∀ k, |inner ℝ (x (k + 1) - z) (B (x (k + 1)) - B (x k))|
      ≤ ((1 + 4 * Fn B lam x ε z 0) * L) * ‖x (k + 1) - x k‖ := by
    intro k
    have a1 := abs_real_inner_le_norm (x (k + 1) - z) (B (x (k + 1)) - B (x k))
    have a2 := hBL (x (k + 1)) (x k)
    have a3 : ‖x (k + 1) - z‖ ≤ 1 + 4 * Fn B lam x ε z 0 := hb k
    calc _ ≤ _ := a1
      _ ≤ (1 + 4 * Fn B lam x ε z 0) * (L * ‖x (k + 1) - x k‖) :=
          mul_le_mul a3 a2 (norm_nonneg _) (by linarith [norm_nonneg (x (k + 1) - z)])
      _ = _ := by ring
  have hl : ∀ k, |lam k| ≤ (1 - 2 * ε) / (2 * L) := by
    intro k
    rw [abs_of_nonneg (hε.le.trans (hlam k).1)]
    exact (hlam k).2
  obtain ⟨r, hr⟩ := norm_conv (Fn B lam x ε z) (fun n => ‖x (n + 1) - x n‖)
    (fun n => ‖x (n + 1) - z‖) (fun n => inner ℝ (x (n + 1) - z) (B (x (n + 1)) - B (x n))) lam
    ε ((1 - 2 * ε) / (2 * L)) ((1 + 4 * Fn B lam x ε z 0) * L) Fl hF hd (fun k => rfl) hQ hl
    (fun _ => norm_nonneg _)
  exact ⟨r, (tendsto_add_atTop_iff_nat 1).mp hr⟩

end Main

end RRAux_FRBSplitting_Weak_theorem_2_5

open Filter Topology RRAux_FRBSplitting_Weak_theorem_2_5 in
open FRBSplitting.Weak in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (L ε : ℝ)
    (hA : IsMaximalMonotone A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B)
    (hL : 0 < L) (hBL : IsLipschitzOp L B)
    (hzer : (zeroSet A B).Nonempty)
    (hε : 0 < ε) (lam : ℕ → ℝ) (hlam : ∀ j, ε ≤ lam j ∧ lam j ≤ (1 - 2 * ε) / (2 * L))
    (x : ℕ → H) (hrun : IsFRBRun J B lam x) :
    ∃ xs ∈ zeroSet A B, IsWeakLimit x xs := by
  obtain ⟨z0, hz0⟩ := hzer
  have hfe := fun z (hz : z ∈ zeroSet A B) =>
    fejer A B J L ε hA hJ hBm hL hBL hε lam hlam x hrun z hz
  have hdd := (hfe z0 hz0).2
  have hdd1 : Tendsto (fun n => ‖x (n + 1 + 1) - x (n + 1)‖) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr hdd
  have hmax : OpialKit.MaxMono (fun y => {w | ∃ a ∈ A y, w = a + B y}) :=
    OpialKit.maxMono_add_lipschitz hA J (fun γ hγ w => hJ γ hγ w) hBm hL hBL
  have hU : Tendsto (fun n => Uop B lam x n) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n => ε⁻¹ * ‖x (n + 1 + 1) - x (n + 1)‖
      + L * ‖x (n + 1 + 1) - x (n + 1)‖
      + (ε⁻¹ * ((1 - 2 * ε) / (2 * L))) * (L * ‖x (n + 1) - x n‖)) (fun n => ?_) ?_
    · unfold Uop
      rw [U_eq _ _ _ _ _ _ _ (lt_of_lt_of_le hε (hlam (n + 1)).1).ne']
      exact U_bound _ _ _ _ _ _ _ _ _ _ _ hε (hlam (n + 1)).1 (hε.le.trans (hlam n).1)
        (hlam n).2 (hBL _ _) (hBL _ _)
    · have h := ((hdd1.const_mul ε⁻¹).add (hdd1.const_mul L)).add
        ((hdd.const_mul L).const_mul (ε⁻¹ * ((1 - 2 * ε) / (2 * L))))
      simp only [mul_zero, add_zero] at h
      exact h
  have hmem : ∀ n, Uop B lam x n ∈ (fun y => {w | ∃ a ∈ A y, w = a + B y}) (x (n + 2)) := by
    intro n
    have hres := hJ (lam (n + 1)) (lt_of_lt_of_le hε (hlam (n + 1)).1)
      (x (n + 1) - lam (n + 1) • B (x (n + 1)) - lam n • (B (x (n + 1)) - B (x n)))
    rw [← hrun n] at hres
    exact ⟨_, hres, rfl⟩
  obtain ⟨p, hp, hw⟩ := OpialKit.opial (zeroSet A B) ⟨z0, hz0⟩ x (fun z hz => (hfe z hz).1)
    (fun φ p hφ hp => by
      have hw : OpialKit.WLim (fun k => x (φ k + 2)) p := by
        refine wlim_shift (x ∘ φ) _ p hp ?_
        refine squeeze_zero (fun _ => norm_nonneg _)
          (g := fun k => ‖x (φ k + 2) - x (φ k + 1)‖ + ‖x (φ k + 1) - x (φ k)‖)
          (fun k => norm_sub_le_norm_sub_add_norm_sub (x (φ k + 2)) (x (φ k + 1)) (x (φ k))) ?_
        have h := (hdd1.comp hφ.tendsto_atTop).add (hdd.comp hφ.tendsto_atTop)
        simp only [add_zero] at h
        exact h
      obtain ⟨a, ha, h0⟩ := OpialKit.MaxMono.demiclosed hmax (x := fun k => x (φ k + 2))
        (u := fun k => Uop B lam x (φ k)) (fun k => hmem (φ k)) hw (hU.comp hφ.tendsto_atTop)
      show -B p ∈ A p
      rwa [← eq_neg_of_add_eq_zero_left h0.symm])
  exact ⟨p, hp, hw⟩

#print axioms solution
