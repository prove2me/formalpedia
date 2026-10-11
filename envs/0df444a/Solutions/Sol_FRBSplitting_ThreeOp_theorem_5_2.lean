-- Prove2me | solution 1 for FRBSplitting.ThreeOp.theorem_5_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T05:56:46.799291+00:00
-- url     : https://prove2.me/submissions/9640b9a0-b5fe-4c8b-bc93-ce7fa3159ca2

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_ThreeOp_Setting
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

namespace RRAux_FRBSplitting_ThreeOp_theorem_5_2

open Filter Topology

lemma real_step (lam L₁ L₂ β n1 n2 e f c IB K M Φ1 Φ2 N I0 : ℝ)
    (hlam : 0 < lam) (hL₁ : 0 ≤ L₁) (hL₂ : 0 < L₂) (hβL : β * L₂ = 1)
    (hmain : 0 ≤ I0 - lam * IB - lam * (K + M) + lam * Φ2 - lam * (Φ1 + N))
    (h0 : 2 * I0 = n1 ^ 2 - n2 ^ 2 - e ^ 2)
    (hIB : 0 ≤ IB) (hK : β * c ^ 2 ≤ K) (hM : -(e * c) ≤ M) (hN : -(e * (L₁ * f)) ≤ N) :
    n2 ^ 2 - 2 * lam * Φ2 + lam * L₁ * e ^ 2 ≤
      n1 ^ 2 - 2 * lam * Φ1 + lam * L₁ * f ^ 2 - (1 - 2 * lam * L₁ - lam * L₂ / 2) * e ^ 2 := by
  have hsq : 0 ≤ lam * L₂ * (2 * β * c - e) ^ 2 := by positivity
  have hid : lam * L₂ * (2 * β * c - e) ^ 2 = lam * (4 * β * c ^ 2 - 4 * e * c + L₂ * e ^ 2) := by
    linear_combination (lam * 4 * β * c ^ 2 - lam * 4 * e * c) * hβL
  have h1 : lam * IB ≥ 0 := mul_nonneg hlam.le hIB
  have h2 : lam * (β * c ^ 2) ≤ lam * K := mul_le_mul_of_nonneg_left hK hlam.le
  have h3 : lam * (-(e * c)) ≤ lam * M := mul_le_mul_of_nonneg_left hM hlam.le
  have h4 : lam * (-(e * (L₁ * f))) ≤ lam * N := mul_le_mul_of_nonneg_left hN hlam.le
  have h5 : 0 ≤ lam * L₁ * (e - f) ^ 2 := by positivity
  nlinarith

lemma lower_E (lam L₁ n e Φ : ℝ) (hlam : 0 < lam) (hL₁ : 0 ≤ L₁) (hlL : lam * L₁ ≤ 1 / 2)
    (hΦ : |Φ| ≤ n * (L₁ * e)) (hn : 0 ≤ n) (he : 0 ≤ e) :
    n ^ 2 / 2 ≤ n ^ 2 - 2 * lam * Φ + lam * L₁ * e ^ 2 := by
  have h1 : Φ ≤ n * (L₁ * e) := le_trans (le_abs_self _) hΦ
  have h2 : lam * Φ ≤ lam * (n * (L₁ * e)) := mul_le_mul_of_nonneg_left h1 hlam.le
  have h3 : 0 ≤ lam * L₁ * (n - e) ^ 2 := by positivity
  have h4 : 0 ≤ (1 / 2 - lam * L₁) * n ^ 2 := mul_nonneg (by linarith) (sq_nonneg n)
  nlinarith

lemma n_le (n E0 : ℝ) (h : n ^ 2 / 2 ≤ E0) : n ≤ 2 * E0 + 1 := by
  nlinarith [sq_nonneg (n - 1)]

lemma lip_of_coco (β L₂ c d : ℝ) (hβ : 0 < β) (hβL : β * L₂ = 1) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : β * c ^ 2 ≤ c * d) : c ≤ L₂ * d := by
  by_contra hcon
  push Not at hcon
  have hc0 : 0 < c := lt_of_le_of_lt (by nlinarith [hβ]) hcon
  have : β * (L₂ * d) < β * c := mul_lt_mul_of_pos_left hcon hβ
  have : d < β * c := by nlinarith
  nlinarith

lemma seq_lim (E n e Φ : ℕ → ℝ) (lam L₁ ε : ℝ) (hε : 0 < ε) (hlam : 0 < lam) (hL₁ : 0 ≤ L₁)
    (hlL : lam * L₁ ≤ 1 / 2)
    (hE : ∀ k, E k = n k ^ 2 - 2 * lam * Φ k + lam * L₁ * e k ^ 2)
    (hstep : ∀ k, E (k + 1) ≤ E k - ε * e (k + 1) ^ 2)
    (hΦ : ∀ k, |Φ k| ≤ n k * (L₁ * e k)) (hn : ∀ k, 0 ≤ n k) (he : ∀ k, 0 ≤ e k) :
    Tendsto e atTop (𝓝 0) ∧ ∃ r, Tendsto n atTop (𝓝 r) := by
  have hlow : ∀ k, n k ^ 2 / 2 ≤ E k := fun k => by
    rw [hE k]; exact lower_E lam L₁ (n k) (e k) (Φ k) hlam hL₁ hlL (hΦ k) (hn k) (he k)
  have hE0 : ∀ k, 0 ≤ E k := fun k => le_trans (by positivity) (hlow k)
  have hanti : Antitone E := antitone_nat_of_succ_le fun k => by
    have := hstep k; have : 0 ≤ ε * e (k + 1) ^ 2 := by positivity
    linarith
  have hlim : Tendsto E atTop (𝓝 (⨅ i, E i)) :=
    tendsto_atTop_ciInf hanti ⟨0, by rintro _ ⟨k, rfl⟩; exact hE0 k⟩
  set ℓ := ⨅ i, E i
  have hdiff : Tendsto (fun k => (E k - E (k + 1)) / ε) atTop (𝓝 0) := by
    have := (hlim.sub (hlim.comp (tendsto_add_atTop_nat 1))).div_const ε
    simpa using this
  have hD1 : Tendsto (fun k => e (k + 1) ^ 2) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiff
      (fun k => by positivity) (fun k => ?_)
    have := hstep k
    rw [le_div_iff₀ hε]; linarith
  have hD : Tendsto (fun k => e k ^ 2) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mp hD1
  have he0 : Tendsto e atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hD
    simp only [Real.sqrt_zero] at this
    refine this.congr fun k => ?_
    simp [Function.comp, Real.sqrt_sq (he k)]
  refine ⟨he0, ?_⟩
  have hnb : ∀ k, n k ≤ 2 * E 0 + 1 := fun k =>
    n_le _ _ (le_trans (hlow k) (hanti (Nat.zero_le k)))
  have hΦ0 : Tendsto Φ atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun k => (2 * E 0 + 1) * L₁ * e k) (fun k => ?_) ?_
    · rw [Real.norm_eq_abs]
      refine le_trans (hΦ k) ?_
      have := mul_le_mul_of_nonneg_right (hnb k) (mul_nonneg hL₁ (he k))
      linarith
    · simpa using he0.const_mul ((2 * E 0 + 1) * L₁)
  have hn2 : Tendsto (fun k => n k ^ 2) atTop (𝓝 ℓ) := by
    have := (hlim.add ((hΦ0.const_mul (2 * lam)))).sub (hD.const_mul (lam * L₁))
    simp only [mul_zero, add_zero, sub_zero] at this
    refine this.congr fun k => ?_
    rw [hE k]; ring
  refine ⟨Real.sqrt ℓ, ?_⟩
  refine ((Real.continuous_sqrt.tendsto ℓ).comp hn2).congr fun k => ?_
  simp [Function.comp, Real.sqrt_sq (hn k)]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma vec_step (A : H → Set H) (B C : H → H) (lam L₁ L₂ : ℝ) (hlam : 0 < lam) (hL₁ : 0 ≤ L₁)
    (hL₂ : 0 < L₂)
    (hAm : ∀ x y u v, u ∈ A x → v ∈ A y → 0 ≤ inner ℝ (x - y) (u - v))
    (hBm : ∀ x y, 0 ≤ inner ℝ (x - y) (B x - B y))
    (hBL : ∀ x y, ‖B x - B y‖ ≤ L₁ * ‖x - y‖)
    (hC : ∀ x y, L₂⁻¹ * ‖C x - C y‖ ^ 2 ≤ inner ℝ (C x - C y) (x - y))
    (xb x0 x1 x2 : H) (hxb : -(B xb + C xb) ∈ A xb)
    (ha : lam⁻¹ • ((x1 - (2 * lam) • B x1 + lam • B x0 - lam • C x1) - x2) ∈ A x2) :
    ‖x2 - xb‖ ^ 2 - 2 * lam * inner ℝ (x2 - xb) (B x2 - B x1) + lam * L₁ * ‖x2 - x1‖ ^ 2 ≤
      ‖x1 - xb‖ ^ 2 - 2 * lam * inner ℝ (x1 - xb) (B x1 - B x0) + lam * L₁ * ‖x1 - x0‖ ^ 2
        - (1 - 2 * lam * L₁ - lam * L₂ / 2) * ‖x2 - x1‖ ^ 2 := by
  have hm := hAm _ _ _ _ ha hxb
  have hv : lam • (lam⁻¹ • ((x1 - (2 * lam) • B x1 + lam • B x0 - lam • C x1) - x2)
      - -(B xb + C xb)) = (x1 - x2) - lam • (B x2 - B xb) - lam • (C x1 - C xb)
        + lam • (B x2 - B x1) - lam • (B x1 - B x0) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
    module
  have hmain : 0 ≤ inner ℝ (x2 - xb) ((x1 - x2) - lam • (B x2 - B xb) - lam • (C x1 - C xb)
        + lam • (B x2 - B x1) - lam • (B x1 - B x0)) := by
    rw [← hv, inner_smul_right]; exact mul_nonneg hlam.le hm
  have h0 : 2 * inner ℝ (x2 - xb) (x1 - x2) = ‖x1 - xb‖ ^ 2 - ‖x2 - xb‖ ^ 2 - ‖x2 - x1‖ ^ 2 := by
    have := norm_add_sq_real (x2 - xb) (x1 - x2)
    rw [show x2 - xb + (x1 - x2) = x1 - xb by abel, norm_sub_rev x1 x2] at this
    linarith
  have hsplit : ∀ w : H, inner ℝ (x2 - xb) w = inner ℝ (x1 - xb) w + inner ℝ (x2 - x1) w := by
    intro w
    rw [← inner_add_left, show x1 - xb + (x2 - x1) = x2 - xb by abel]
  have hexp : inner ℝ (x2 - xb) ((x1 - x2) - lam • (B x2 - B xb) - lam • (C x1 - C xb)
        + lam • (B x2 - B x1) - lam • (B x1 - B x0)) =
      inner ℝ (x2 - xb) (x1 - x2) - lam * inner ℝ (x2 - xb) (B x2 - B xb)
        - lam * (inner ℝ (x1 - xb) (C x1 - C xb) + inner ℝ (x2 - x1) (C x1 - C xb))
        + lam * inner ℝ (x2 - xb) (B x2 - B x1)
        - lam * (inner ℝ (x1 - xb) (B x1 - B x0) + inner ℝ (x2 - x1) (B x1 - B x0)) := by
    rw [← hsplit (C x1 - C xb), ← hsplit (B x1 - B x0)]
    simp only [inner_add_right, inner_sub_right, inner_smul_right]
  rw [hexp] at hmain
  have hK : L₂⁻¹ * ‖C x1 - C xb‖ ^ 2 ≤ inner ℝ (x1 - xb) (C x1 - C xb) := by
    rw [real_inner_comm]; exact hC x1 xb
  have hM : -(‖x2 - x1‖ * ‖C x1 - C xb‖) ≤ inner ℝ (x2 - x1) (C x1 - C xb) :=
    neg_le_of_abs_le (abs_real_inner_le_norm _ _)
  have hN : -(‖x2 - x1‖ * (L₁ * ‖x1 - x0‖)) ≤ inner ℝ (x2 - x1) (B x1 - B x0) := by
    have h1 := neg_le_of_abs_le (abs_real_inner_le_norm (x2 - x1) (B x1 - B x0))
    have h2 : ‖x2 - x1‖ * ‖B x1 - B x0‖ ≤ ‖x2 - x1‖ * (L₁ * ‖x1 - x0‖) :=
      mul_le_mul_of_nonneg_left (hBL x1 x0) (norm_nonneg _)
    linarith
  exact real_step lam L₁ L₂ L₂⁻¹ _ _ _ _ _ _ _ _ _ _ _ _ hlam hL₁ hL₂
    (inv_mul_cancel₀ hL₂.ne') hmain h0 (hBm x2 xb) hK hM hN

lemma resid_bound (B C : H → H) (lam L₁ L₂ : ℝ) (hlam : 0 < lam) (hL₁ : 0 ≤ L₁) (hL₂ : 0 < L₂)
    (hBL : ∀ x y, ‖B x - B y‖ ≤ L₁ * ‖x - y‖) (hCL : ∀ x y, ‖C x - C y‖ ≤ L₂ * ‖x - y‖)
    (x0 x1 x2 : H) :
    ‖lam⁻¹ • ((x1 - (2 * lam) • B x1 + lam • B x0 - lam • C x1) - x2) + (B x2 + C x2)‖ ≤
      lam⁻¹ * ((1 + lam * L₁ + lam * L₂) * ‖x2 - x1‖ + lam * L₁ * ‖x1 - x0‖) := by
  have hv : lam⁻¹ • ((x1 - (2 * lam) • B x1 + lam • B x0 - lam • C x1) - x2) + (B x2 + C x2)
      = lam⁻¹ • ((x1 - x2) + lam • (B x2 - B x1) - lam • (B x1 - B x0)
        + lam • (C x2 - C x1)) := by
    have hne := hlam.ne'
    rw [eq_inv_smul_iff₀ hne, smul_add, smul_smul, mul_inv_cancel₀ hne, one_smul]
    module
  rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam)]
  refine mul_le_mul_of_nonneg_left ?_ (inv_pos.mpr hlam).le
  have t1 := norm_add_le ((x1 - x2) + lam • (B x2 - B x1) - lam • (B x1 - B x0))
    (lam • (C x2 - C x1))
  have t2 := norm_sub_le ((x1 - x2) + lam • (B x2 - B x1)) (lam • (B x1 - B x0))
  have t3 := norm_add_le (x1 - x2) (lam • (B x2 - B x1))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at t1 t2 t3
  have b1 := mul_le_mul_of_nonneg_left (hBL x2 x1) hlam.le
  have b2 := mul_le_mul_of_nonneg_left (hBL x1 x0) hlam.le
  have b3 := mul_le_mul_of_nonneg_left (hCL x2 x1) hlam.le
  rw [norm_sub_rev x1 x2] at t3
  nlinarith

end RRAux_FRBSplitting_ThreeOp_theorem_5_2

open FRBSplitting.ThreeOp in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (B C : H → H) (J : ℝ → H → H) (L₁ L₂ lam : ℝ)
    (hA : IsMaximalMonotone A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B)
    (hL₁ : 0 ≤ L₁) (hBL : IsLipschitzOp L₁ B)
    (hL₂ : 0 < L₂) (hC : IsCocoercive L₂⁻¹ C)
    (hzer : (FRBSplitting.Weak.zeroSet A (fun y => B y + C y)).Nonempty)
    (hlam0 : 0 < lam) (hlam1 : lam < 2 / (4 * L₁ + L₂))
    (x : ℕ → H) (hrun : IsThreeOpRun J B C lam x) :
    ∃ xs ∈ FRBSplitting.Weak.zeroSet A (fun y => B y + C y), FRBSplitting.Weak.IsWeakLimit x xs := by
  open RRAux_FRBSplitting_ThreeOp_theorem_5_2 Filter Topology in
  have hden : 0 < 4 * L₁ + L₂ := by linarith
  have hlt : lam * (4 * L₁ + L₂) < 2 := by
    have h := (lt_div_iff₀ hden).mp hlam1
    linarith [mul_comm lam (4 * L₁ + L₂)]
  have hexp : lam * (4 * L₁ + L₂) = 4 * (lam * L₁) + lam * L₂ := by ring
  have hpos : 0 < lam * L₂ := mul_pos hlam0 hL₂
  have hε : 0 < 1 - 2 * lam * L₁ - lam * L₂ / 2 := by
    have : 2 * lam * L₁ = 2 * (lam * L₁) := by ring
    linarith
  have hlL : lam * L₁ ≤ 1 / 2 := by linarith
  have hAm : ∀ x y u v, u ∈ A x → v ∈ A y → 0 ≤ inner ℝ (x - y) (u - v) := hA.1
  have hC' : ∀ x y, L₂⁻¹ * ‖C x - C y‖ ^ 2 ≤ inner ℝ (C x - C y) (x - y) := hC
  have hCL : ∀ x y, ‖C x - C y‖ ≤ L₂ * ‖x - y‖ := fun x y => by
    apply lip_of_coco L₂⁻¹ L₂ _ _ (inv_pos.mpr hL₂) (inv_mul_cancel₀ hL₂.ne') (norm_nonneg _)
      (norm_nonneg _)
    exact le_trans (hC x y) (real_inner_le_norm _ _)
  have hres : ∀ k, lam⁻¹ • ((x (k + 1) - (2 * lam) • B (x (k + 1)) + lam • B (x k)
      - lam • C (x (k + 1))) - x (k + 2)) ∈ A (x (k + 2)) := by
    intro k; rw [hrun k]; exact hJ lam hlam0 _
  have hkey : ∀ z ∈ FRBSplitting.Weak.zeroSet A (fun y => B y + C y),
      Tendsto (fun k => ‖x (k + 1) - x k‖) atTop (𝓝 0) ∧
        ∃ r, Tendsto (fun k => ‖x (k + 1) - z‖) atTop (𝓝 r) := by
    intro z hz
    have hz' : -(B z + C z) ∈ A z := hz
    refine seq_lim
      (fun k => ‖x (k + 1) - z‖ ^ 2 - 2 * lam * inner ℝ (x (k + 1) - z) (B (x (k + 1)) - B (x k))
        + lam * L₁ * ‖x (k + 1) - x k‖ ^ 2)
      (fun k => ‖x (k + 1) - z‖) (fun k => ‖x (k + 1) - x k‖)
      (fun k => inner ℝ (x (k + 1) - z) (B (x (k + 1)) - B (x k))) lam L₁ _ hε hlam0 hL₁ hlL
      (fun k => rfl) (fun k => ?_) (fun k => ?_) (fun k => norm_nonneg _) (fun k => norm_nonneg _)
    · exact vec_step A B C lam L₁ L₂ hlam0 hL₁ hL₂ hAm hBm hBL hC' z (x k) (x (k + 1)) (x (k + 2))
        hz' (hres k)
    · refine le_trans (abs_real_inner_le_norm _ _) ?_
      exact mul_le_mul_of_nonneg_left (hBL _ _) (norm_nonneg _)
  obtain ⟨xb, hxb⟩ := hzer
  have hreg := (hkey xb hxb).1
  have hBCm : ∀ x y, 0 ≤ inner ℝ (x - y) ((fun y => B y + C y) x - (fun y => B y + C y) y) := by
    intro x y
    show 0 ≤ inner ℝ (x - y) ((B x + C x) - (B y + C y))
    rw [show (B x + C x) - (B y + C y) = (B x - B y) + (C x - C y) by abel, inner_add_right,
      real_inner_comm (C x - C y) (x - y)]
    have h1 := hBm x y
    have h2 := hC' x y
    have h3 : 0 ≤ L₂⁻¹ * ‖C x - C y‖ ^ 2 := by positivity
    linarith
  have hBCL : ∀ x y, ‖(fun y => B y + C y) x - (fun y => B y + C y) y‖ ≤ (L₁ + L₂) * ‖x - y‖ := by
    intro x y
    show ‖(B x + C x) - (B y + C y)‖ ≤ (L₁ + L₂) * ‖x - y‖
    rw [show (B x + C x) - (B y + C y) = (B x - B y) + (C x - C y) by abel]
    have := norm_add_le (B x - B y) (C x - C y)
    have := hBL x y
    have := hCL x y
    linarith
  have hAmax : OpialKit.MaxMono A := hA
  have hT := OpialKit.maxMono_add_lipschitz hAmax J (fun γ hγ z => hJ γ hγ z) hBCm
    (by linarith : (0 : ℝ) < L₁ + L₂) hBCL
  have hclu : ∀ (φ : ℕ → ℕ) (p : H), StrictMono φ → OpialKit.WLim (x ∘ φ) p →
      p ∈ FRBSplitting.Weak.zeroSet A (fun y => B y + C y) := by
    intro φ p hφ hp
    have hle : ∀ n, n ≤ φ n := fun n => hφ.id_le n
    have hψ2 : ∀ n, φ (n + 2) - 2 + 2 = φ (n + 2) := fun n =>
      Nat.sub_add_cancel (le_trans (by omega) (hle (n + 2)))
    have hψt : Tendsto (fun n => φ (n + 2) - 2) atTop atTop :=
      tendsto_atTop_mono (fun n => by have := hle (n + 2); show n ≤ φ (n + 2) - 2; omega) tendsto_id
    have hwl : OpialKit.WLim (fun n => x (φ (n + 2) - 2 + 2)) p := by
      have := OpialKit.wlim_comp hp (strictMono_id.add_const 2)
      simp only [hψ2]
      exact this
    let v : ℕ → H := fun k => lam⁻¹ • ((x (k + 1) - (2 * lam) • B (x (k + 1)) + lam • B (x k)
      - lam • C (x (k + 1))) - x (k + 2)) + (B (x (k + 2)) + C (x (k + 2)))
    have hv0 : Tendsto v atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => resid_bound B C lam L₁ L₂ hlam0 hL₁ hL₂ hBL hCL
        (x k) (x (k + 1)) (x (k + 2))) ?_
      have h1 := (tendsto_add_atTop_iff_nat 1).mpr hreg
      have := ((h1.const_mul (1 + lam * L₁ + lam * L₂)).add (hreg.const_mul (lam * L₁))).const_mul
        lam⁻¹
      simpa using this
    have hmem : ∀ n, v (φ (n + 2) - 2) ∈
        (fun x => {w | ∃ a ∈ A x, w = a + (fun y => B y + C y) x}) (x (φ (n + 2) - 2 + 2)) :=
      fun n => ⟨_, hres (φ (n + 2) - 2), rfl⟩
    obtain ⟨a, ha, ha0⟩ := OpialKit.MaxMono.demiclosed hT hmem hwl (hv0.comp hψt)
    show -(B p + C p) ∈ A p
    have : a = -(B p + C p) := eq_neg_of_add_eq_zero_left ha0.symm
    rwa [← this]
  have hfej : ∀ z ∈ FRBSplitting.Weak.zeroSet A (fun y => B y + C y),
      ∃ r : ℝ, Tendsto (fun n => ‖x n - z‖) atTop (𝓝 r) := fun z hz => by
    obtain ⟨r, hr⟩ := (hkey z hz).2
    exact ⟨r, (tendsto_add_atTop_iff_nat 1).mp hr⟩
  obtain ⟨p, hp, hpw⟩ := OpialKit.opial _ ⟨xb, hxb⟩ x hfej hclu
  exact ⟨p, hp, hpw⟩

#print axioms solution
