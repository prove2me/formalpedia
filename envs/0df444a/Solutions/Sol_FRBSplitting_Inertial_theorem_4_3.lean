-- Prove2me | solution 1 for FRBSplitting.Inertial.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:07:14.088747+00:00
-- url     : https://prove2.me/submissions/d5e0526f-2cfd-4658-b316-dc226391f108

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Inertial_Setting
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

namespace RRAux_FRBSplitting_Inertial_theorem_4_3

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem young_aux (K a b c : ℝ) (hK : 0 ≤ K) (hc : c ≤ K * a * b) :
    c ≤ K / 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [mul_nonneg hK (sq_nonneg (a - b))]

theorem step_pure (u d d0 e1 e2 G1 : H) (α β lam K : ℝ) (hβ : 0 < β)
    (hI : 0 ≤ inner ℝ (β • u + d) (-d - (lam * β) • e1 - G1))
    (hY : -inner ℝ d G1 ≤ K / 2 * (‖d‖ ^ 2 + ‖d0‖ ^ 2)) :
    (1 - α) * ‖u + d‖ ^ 2 + 2 * lam * (1 - β) * inner ℝ (u + d) e2
      - 2 * inner ℝ (u + d) (lam • (e2 - e1) - α • d) + K / β * ‖d‖ ^ 2
      + (2 - β - α * β - 2 * K) / β * ‖d‖ ^ 2 + 2 * lam * β * inner ℝ (u + d) e2
    ≤ (1 - α) * ‖u‖ ^ 2 + 2 * lam * (1 - β) * inner ℝ u e1 - 2 * inner ℝ u G1
      + K / β * ‖d0‖ ^ 2 := by
  rw [norm_add_sq_real]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_neg_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq] at hI ⊢
  have hc : inner ℝ d u = inner ℝ u d := real_inner_comm u d
  have key : (1 - α) * ‖u‖ ^ 2 + 2 * lam * (1 - β) * inner ℝ u e1 - 2 * inner ℝ u G1
      + K / β * ‖d0‖ ^ 2 - ((1 - α) * (‖u‖ ^ 2 + 2 * inner ℝ u d + ‖d‖ ^ 2)
      + 2 * lam * (1 - β) * (inner ℝ u e2 + inner ℝ d e2)
      - 2 * (lam * (inner ℝ u e2 - inner ℝ u e1) - α * inner ℝ u d
          + (lam * (inner ℝ d e2 - inner ℝ d e1) - α * ‖d‖ ^ 2))
      + K / β * ‖d‖ ^ 2 + (2 - β - α * β - 2 * K) / β * ‖d‖ ^ 2
      + 2 * lam * β * (inner ℝ u e2 + inner ℝ d e2))
      = (2 / β) * ((β * (-inner ℝ u d - lam * β * inner ℝ u e1 - inner ℝ u G1)
          + (-‖d‖ ^ 2 - lam * β * inner ℝ d e1 - inner ℝ d G1))
        + (K / 2 * (‖d‖ ^ 2 + ‖d0‖ ^ 2) + inner ℝ d G1)) := by
    field_simp
    ring
  have h2 : 0 ≤ (2 / β) * ((β * (-inner ℝ u d - lam * β * inner ℝ u e1 - inner ℝ u G1)
          + (-‖d‖ ^ 2 - lam * β * inner ℝ d e1 - inner ℝ d G1))
        + (K / 2 * (‖d‖ ^ 2 + ‖d0‖ ^ 2) + inner ℝ d G1)) :=
    mul_nonneg (by positivity) (by linarith)
  linarith [hc]

theorem lower_aux (α β lam K a b s v : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hlam : 0 < lam)
    (hK : 0 ≤ K) (hs : 0 ≤ s) (hv : v ≤ K * a * b) :
    (1 - α - K * β) * a ^ 2 ≤ (1 - α) * a ^ 2 + 2 * lam * (1 - β) * s - 2 * v + K / β * b ^ 2 := by
  have h := mul_nonneg (div_nonneg hK hβ0.le) (sq_nonneg (b - β * a))
  have e : K / β * (b - β * a) ^ 2 = K / β * b ^ 2 - 2 * (K * a * b) + K * β * a ^ 2 := by
    field_simp
    ring
  have h3 : 0 ≤ 2 * lam * (1 - β) * s := by
    have : 0 ≤ 1 - β := by linarith
    positivity
  nlinarith

theorem summable_aux (E a : ℕ → ℝ) (hE : ∀ n, 0 ≤ E n) (ha : ∀ n, 0 ≤ a n)
    (h : ∀ n, E (n + 1) + a n ≤ E n) : Tendsto a atTop (𝓝 0) := by
  have hs : ∀ n, ∑ i ∈ Finset.range n, a i ≤ E 0 - E n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ]; linarith [h n]
  exact (summable_of_sum_range_le ha (fun n => by linarith [hs n, hE n])).tendsto_atTop_zero

theorem sqrt_tendsto_aux (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (r : ℝ)
    (h : Tendsto (fun n => f n ^ 2) atTop (𝓝 r)) :
    Tendsto f atTop (𝓝 (Real.sqrt r)) := by
  have := h.sqrt
  simpa [Real.sqrt_sq (hf _)] using this

theorem core (A : H → Set H) (B : H → H) (J : ℝ → H → H) (α β lam K : ℝ) (x z : ℕ → H) (p : H)
    (hAm : ∀ x y u v, u ∈ A x → v ∈ A y → 0 ≤ inner ℝ (x - y) (u - v))
    (hJ : ∀ γ : ℝ, 0 < γ → ∀ w, γ⁻¹ • (w - J γ w) ∈ A (J γ w))
    (hBm : ∀ x y, 0 ≤ inner ℝ (x - y) (B x - B y))
    (hG : ∀ x y, ‖(lam • B x - α • x) - (lam • B y - α • y)‖ ≤ K * ‖x - y‖)
    (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hlam : 0 < lam) (hK0 : 0 ≤ K)
    (hK1 : 2 * K < 2 - β - α * β) (hK2 : K * β < 1 - α)
    (hrun : ∀ k : ℕ, z (k + 2) = J lam (x (k + 1) - lam • B (x (k + 1))
      - (lam / β) • (B (x (k + 1)) - B (x k)) + (α / β) • (x (k + 1) - x k)) ∧
      x (k + 2) = (1 - β) • x (k + 1) + β • z (k + 2))
    (hp : -B p ∈ A p) :
    (∃ r, Tendsto (fun n => ‖x n - p‖) atTop (𝓝 r)) ∧
      Tendsto (fun n => ‖x (n + 1) - x n‖) atTop (𝓝 0) := by
  set G : H → H := fun y => lam • B y - α • y with hGdef
  let S : ℕ → ℝ := fun n => inner ℝ (x n - p) (B (x n) - B p)
  let V : ℕ → ℝ := fun n => inner ℝ (x (n + 1) - p) (G (x (n + 1)) - G (x n))
  let D : ℕ → ℝ := fun n => ‖x (n + 1) - x n‖
  let E : ℕ → ℝ := fun n => (1 - α) * ‖x (n + 1) - p‖ ^ 2 + 2 * lam * (1 - β) * S (n + 1)
    - 2 * V n + K / β * D n ^ 2
  have hS : ∀ n, 0 ≤ S n := fun n => hBm _ _
  have hGl : ∀ x y, ‖G x - G y‖ ≤ K * ‖x - y‖ := hG
  -- one step of the Lyapunov inequality
  have hstep : ∀ n, E (n + 1) + (2 - β - α * β - 2 * K) / β * D (n + 1) ^ 2
      + 2 * lam * β * S (n + 2) ≤ E n := by
    intro n
    obtain ⟨hz, hx⟩ := hrun n
    have ha := hJ lam hlam (x (n + 1) - lam • B (x (n + 1))
      - (lam / β) • (B (x (n + 1)) - B (x n)) + (α / β) • (x (n + 1) - x n))
    rw [← hz] at ha
    have hmon := hAm _ _ _ _ ha hp
    have hI : 0 ≤ inner ℝ (β • (x (n + 1) - p) + (x (n + 2) - x (n + 1)))
        (-(x (n + 2) - x (n + 1)) - (lam * β) • (B (x (n + 1)) - B p)
          - (G (x (n + 1)) - G (x n))) := by
      have e1 : β • (x (n + 1) - p) + (x (n + 2) - x (n + 1)) = β • (z (n + 2) - p) := by
        rw [hx]; module
      have e2 : -(x (n + 2) - x (n + 1)) - (lam * β) • (B (x (n + 1)) - B p)
          - (G (x (n + 1)) - G (x n)) = (lam * β) • (lam⁻¹ • ((x (n + 1) - lam • B (x (n + 1))
          - (lam / β) • (B (x (n + 1)) - B (x n)) + (α / β) • (x (n + 1) - x n)) - z (n + 2))
          - -B p) := by
        rw [hx, hGdef]
        match_scalars <;> field_simp <;> ring
      rw [e1, e2, real_inner_smul_left, real_inner_smul_right]
      have : 0 ≤ lam * β := by positivity
      exact mul_nonneg hβ0.le (mul_nonneg this hmon)
    have hY : -inner ℝ (x (n + 2) - x (n + 1)) (G (x (n + 1)) - G (x n))
        ≤ K / 2 * (‖x (n + 2) - x (n + 1)‖ ^ 2 + ‖x (n + 1) - x n‖ ^ 2) := by
      apply young_aux _ _ _ _ hK0
      have h1 := neg_le_abs (inner ℝ (x (n + 2) - x (n + 1)) (G (x (n + 1)) - G (x n)))
      have h2 := abs_real_inner_le_norm (x (n + 2) - x (n + 1)) (G (x (n + 1)) - G (x n))
      have h3 := mul_le_mul_of_nonneg_left (hGl (x (n + 1)) (x n))
        (norm_nonneg (x (n + 2) - x (n + 1)))
      linarith
    have h := step_pure (x (n + 1) - p) (x (n + 2) - x (n + 1)) (x (n + 1) - x n)
      (B (x (n + 1)) - B p) (B (x (n + 2)) - B p) (G (x (n + 1)) - G (x n)) α β lam K hβ0 hI hY
    have q1 : x (n + 1) - p + (x (n + 2) - x (n + 1)) = x (n + 2) - p := by abel
    have q2 : lam • (B (x (n + 2)) - B p - (B (x (n + 1)) - B p)) - α • (x (n + 2) - x (n + 1))
        = G (x (n + 2)) - G (x (n + 1)) := by
      rw [hGdef]; module
    rw [q1, q2] at h
    simp only [E, S, V, D]
    linarith
  have hc : 0 < (2 - β - α * β - 2 * K) / β := div_pos (by linarith) hβ0
  have hm : 0 < 1 - α - K * β := by linarith
  have hVb : ∀ n, V n ≤ K * ‖x (n + 1) - p‖ * D n := by
    intro n
    have h2 := real_inner_le_norm (x (n + 1) - p) (G (x (n + 1)) - G (x n))
    have h3 := mul_le_mul_of_nonneg_left (hGl (x (n + 1)) (x n)) (norm_nonneg (x (n + 1) - p))
    simp only [V, D]
    nlinarith
  have hlow : ∀ n, (1 - α - K * β) * ‖x (n + 1) - p‖ ^ 2 ≤ E n := fun n =>
    lower_aux α β lam K _ _ _ _ hβ0 hβ1 hlam hK0 (hS _) (hVb n)
  have hE0 : ∀ n, 0 ≤ E n := fun n => le_trans (by positivity) (hlow n)
  have hSnn : ∀ n, 0 ≤ 2 * lam * β * S (n + 2) := fun n => by
    have := hS (n + 2); positivity
  have hDnn : ∀ n, 0 ≤ (2 - β - α * β - 2 * K) / β * D (n + 1) ^ 2 := fun n => by positivity
  have hanti : Antitone E := antitone_nat_of_succ_le (fun n => by
    linarith [hstep n, hSnn n, hDnn n])
  -- D → 0
  have hD2 : Tendsto (fun n => (2 - β - α * β - 2 * K) / β * D (n + 1) ^ 2) atTop (𝓝 0) :=
    summable_aux E _ hE0 hDnn (fun n => by linarith [hstep n, hSnn n])
  have hD2' : Tendsto (fun n => D (n + 1) ^ 2) atTop (𝓝 0) := by
    have := hD2.const_mul ((2 - β - α * β - 2 * K) / β)⁻¹
    simp only [mul_zero] at this
    refine this.congr (fun n => ?_)
    exact inv_mul_cancel_left₀ hc.ne' _
  have hD : Tendsto D atTop (𝓝 0) := by
    have := sqrt_tendsto_aux (fun n => D (n + 1)) (fun n => norm_nonneg _) 0 hD2'
    rw [Real.sqrt_zero] at this
    exact (Filter.tendsto_add_atTop_iff_nat 1).mp this
  -- S → 0
  have hS2 : Tendsto (fun n => 2 * lam * β * S (n + 2)) atTop (𝓝 0) :=
    summable_aux E _ hE0 hSnn (fun n => by linarith [hstep n, hDnn n])
  have hS1 : Tendsto (fun n => S (n + 1)) atTop (𝓝 0) := by
    have := hS2.const_mul (2 * lam * β)⁻¹
    simp only [mul_zero] at this
    have h' : Tendsto (fun n => S (n + 2)) atTop (𝓝 0) := by
      refine this.congr (fun n => ?_)
      have : 2 * lam * β ≠ 0 := by positivity
      field_simp
    exact (Filter.tendsto_add_atTop_iff_nat 1).mp h'
  -- E converges
  have hEl : Tendsto E atTop (𝓝 (⨅ i, E i)) :=
    tendsto_atTop_ciInf hanti ⟨0, by rintro _ ⟨n, rfl⟩; exact hE0 n⟩
  -- boundedness and V → 0
  have hbd : ∀ n, ‖x (n + 1) - p‖ ≤ Real.sqrt (E 0 / (1 - α - K * β)) := by
    intro n
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hm]
    linarith [hlow n, hanti (Nat.zero_le n)]
  have hV : Tendsto V atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => K * Real.sqrt (E 0 / (1 - α - K * β)) * D n) atTop (𝓝 0) := by
      simpa using hD.const_mul (K * Real.sqrt (E 0 / (1 - α - K * β)))
    apply squeeze_zero_norm _ hlim
    intro n
    have h2 := abs_real_inner_le_norm (x (n + 1) - p) (G (x (n + 1)) - G (x n))
    have h3 := mul_le_mul_of_nonneg_left (hGl (x (n + 1)) (x n)) (norm_nonneg (x (n + 1) - p))
    have h4 := mul_le_mul_of_nonneg_right (hbd n) (mul_nonneg hK0 (norm_nonneg (x (n + 1) - x n)))
    rw [Real.norm_eq_abs]
    simp only [V, D]
    nlinarith
  -- φ converges
  have hphi : Tendsto (fun n => ‖x (n + 1) - p‖ ^ 2) atTop
      (𝓝 ((⨅ i, E i) / (1 - α))) := by
    have hlim : Tendsto (fun n => (E n - 2 * lam * (1 - β) * S (n + 1) + 2 * V n
        - K / β * D n ^ 2) / (1 - α)) atTop
        (𝓝 (((⨅ i, E i) - 2 * lam * (1 - β) * 0 + 2 * 0 - K / β * 0 ^ 2) / (1 - α))) :=
      ((((hEl.sub (hS1.const_mul _)).add (hV.const_mul _)).sub
        ((hD.pow 2).const_mul _)).div_const _)
    simp only [mul_zero, add_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at hlim
    refine hlim.congr (fun n => ?_)
    have : (1 - α) ≠ 0 := by linarith
    simp only [E]
    field_simp
    ring
  refine ⟨⟨Real.sqrt ((⨅ i, E i) / (1 - α)), ?_⟩, hD⟩
  have := sqrt_tendsto_aux (fun n => ‖x (n + 1) - p‖) (fun n => norm_nonneg _) _ hphi
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp this

theorem cluster [CompleteSpace H] (A : H → Set H) (B : H → H) (J : ℝ → H → H) (α β lam L : ℝ)
    (x z : ℕ → H)
    (hT : OpialKit.MaxMono (fun y => {w | ∃ a ∈ A y, w = a + B y}))
    (hJ : ∀ γ : ℝ, 0 < γ → ∀ w, γ⁻¹ • (w - J γ w) ∈ A (J γ w))
    (hBL : ∀ x y, ‖B x - B y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L) (hα0 : 0 ≤ α) (hβ0 : 0 < β) (hlam : 0 < lam)
    (hrun : ∀ k : ℕ, z (k + 2) = J lam (x (k + 1) - lam • B (x (k + 1))
      - (lam / β) • (B (x (k + 1)) - B (x k)) + (α / β) • (x (k + 1) - x k)) ∧
      x (k + 2) = (1 - β) • x (k + 1) + β • z (k + 2))
    (hD : Tendsto (fun n => ‖x (n + 1) - x n‖) atTop (𝓝 0))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (q : H) (hq : OpialKit.WLim (x ∘ φ) q) :
    -B q ∈ A q := by
  let w : ℕ → H := fun k => x (k + 1) - lam • B (x (k + 1))
      - (lam / β) • (B (x (k + 1)) - B (x k)) + (α / β) • (x (k + 1) - x k)
  let D : ℕ → ℝ := fun n => ‖x (n + 1) - x n‖
  have hD1 : Tendsto (fun n => D (n + 1)) atTop (𝓝 0) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr hD
  have hzx : ∀ k, z (k + 2) - x (k + 1) = β⁻¹ • (x (k + 2) - x (k + 1)) := by
    intro k
    rw [(hrun k).2]
    match_scalars <;> field_simp <;> ring
  have hnz : ∀ k, ‖z (k + 2) - x (k + 1)‖ = β⁻¹ * D (k + 1) := by
    intro k
    rw [hzx k, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hβ0)]
  -- z (k+2) - x k → 0
  have hr : Tendsto (fun k => z (k + 2) - x k) atTop (𝓝 0) := by
    have hlim : Tendsto (fun k => β⁻¹ * D (k + 1) + D k) atTop (𝓝 0) := by
      simpa using (hD1.const_mul β⁻¹).add hD
    refine squeeze_zero_norm (fun k => ?_) hlim
    have e : z (k + 2) - x k = (z (k + 2) - x (k + 1)) + (x (k + 1) - x k) := by abel
    rw [e, ← hnz k]
    exact norm_add_le _ _
  -- the residual
  let f : ℕ → H := fun k => lam⁻¹ • (w k - z (k + 2)) + B (z (k + 2))
  have hf : Tendsto f atTop (𝓝 0) := by
    have hlim : Tendsto (fun k => lam⁻¹ * (β⁻¹ * D (k + 1)) + β⁻¹ * (L * D k)
        + α / (lam * β) * D k + L * (β⁻¹ * D (k + 1))) atTop (𝓝 0) := by
      have := ((((hD1.const_mul β⁻¹).const_mul lam⁻¹).add ((hD.const_mul L).const_mul β⁻¹)).add
        (hD.const_mul (α / (lam * β)))).add ((hD1.const_mul β⁻¹).const_mul L)
      simpa using this
    refine squeeze_zero_norm (fun k => ?_) hlim
    have e : f k = lam⁻¹ • (x (k + 1) - z (k + 2)) - β⁻¹ • (B (x (k + 1)) - B (x k))
        + (α / (lam * β)) • (x (k + 1) - x k) + (B (z (k + 2)) - B (x (k + 1))) := by
      simp only [f, w]
      match_scalars <;> field_simp <;> ring
    rw [e]
    have b1 : ‖lam⁻¹ • (x (k + 1) - z (k + 2))‖ = lam⁻¹ * (β⁻¹ * D (k + 1)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam), norm_sub_rev, hnz k]
    have b2 : ‖β⁻¹ • (B (x (k + 1)) - B (x k))‖ ≤ β⁻¹ * (L * D k) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hβ0)]
      exact mul_le_mul_of_nonneg_left (hBL _ _) (inv_pos.mpr hβ0).le
    have b3 : ‖(α / (lam * β)) • (x (k + 1) - x k)‖ ≤ α / (lam * β) * D k := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have b4 : ‖B (z (k + 2)) - B (x (k + 1))‖ ≤ L * (β⁻¹ * D (k + 1)) := by
      rw [← hnz k]; exact hBL _ _
    calc _ ≤ ‖lam⁻¹ • (x (k + 1) - z (k + 2)) - β⁻¹ • (B (x (k + 1)) - B (x k))
          + (α / (lam * β)) • (x (k + 1) - x k)‖ + ‖B (z (k + 2)) - B (x (k + 1))‖ :=
          norm_add_le _ _
      _ ≤ ‖lam⁻¹ • (x (k + 1) - z (k + 2)) - β⁻¹ • (B (x (k + 1)) - B (x k))‖
          + ‖(α / (lam * β)) • (x (k + 1) - x k)‖ + ‖B (z (k + 2)) - B (x (k + 1))‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ ‖lam⁻¹ • (x (k + 1) - z (k + 2))‖ + ‖β⁻¹ • (B (x (k + 1)) - B (x k))‖
          + ‖(α / (lam * β)) • (x (k + 1) - x k)‖ + ‖B (z (k + 2)) - B (x (k + 1))‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ _ := by rw [b1]; linarith [b2, b3, b4]
  have hmem : ∀ n, f (φ n) ∈ (fun y => {w | ∃ a ∈ A y, w = a + B y}) (z (φ n + 2)) := by
    intro n
    refine ⟨lam⁻¹ • (w (φ n) - z (φ n + 2)), ?_, rfl⟩
    have h := hJ lam hlam (w (φ n))
    rw [← (hrun (φ n)).1] at h
    exact h
  have hzw : OpialKit.WLim (fun n => z (φ n + 2)) q := by
    intro v
    have h1 := hq v
    have h2 : Tendsto (fun n => inner ℝ (z (φ n + 2) - x (φ n)) v) atTop (𝓝 0) := by
      have := Filter.Tendsto.inner (𝕜 := ℝ) (hr.comp hφ.tendsto_atTop) (tendsto_const_nhds (x := v))
      simpa using this
    have := h1.add h2
    rw [add_zero] at this
    refine this.congr (fun n => ?_)
    simp only [Function.comp, ← inner_add_left]
    congr 1
    abel
  have h0 := OpialKit.MaxMono.demiclosed hT hmem hzw (hf.comp hφ.tendsto_atTop)
  obtain ⟨a, ha, h0⟩ := h0
  have : a = -B q := eq_neg_of_add_eq_zero_left h0.symm
  rw [← this]; exact ha

theorem params1 (α β lam L : ℝ) (hβ0 : 0 < β) (hlam : 0 < lam) (hL : 0 < L)
    (h1 : lam < (2 - β - α * β - 2 * α) / (2 * L)) (h2 : lam < (1 - α - α * β) / (β * L)) :
    2 * (lam * L + α) < 2 - β - α * β ∧ (lam * L + α) * β < 1 - α := by
  rw [lt_div_iff₀ (by positivity)] at h1 h2
  constructor <;> nlinarith

theorem params2 (α β lam L : ℝ) (hα0 : 0 ≤ α) (hβ0 : 0 < β) (hlam : 0 < lam) (hL : 0 < L)
    (h0 : α < (2 - β) / (2 + β))
    (h1 : lam < (2 - β - α * β + 2 * α) / (2 * L)) (h2 : lam < (1 - α + α * β) / (β * L)) :
    2 * max (lam * L - α) α < 2 - β - α * β ∧ max (lam * L - α) α * β < 1 - α := by
  rw [lt_div_iff₀ (by positivity)] at h0 h1 h2
  rcases le_total (lam * L - α) α with h | h
  · rw [max_eq_right h]; constructor <;> nlinarith
  · rw [max_eq_left h]; constructor <;> nlinarith

theorem glip1 (B : H → H) (α lam L : ℝ) (hα0 : 0 ≤ α) (hlam : 0 < lam)
    (hBL : ∀ x y, ‖B x - B y‖ ≤ L * ‖x - y‖) (x y : H) :
    ‖(lam • B x - α • x) - (lam • B y - α • y)‖ ≤ (lam * L + α) * ‖x - y‖ := by
  have e : (lam • B x - α • x) - (lam • B y - α • y) = lam • (B x - B y) - α • (x - y) := by
    module
  rw [e]
  calc _ ≤ ‖lam • (B x - B y)‖ + ‖α • (x - y)‖ := norm_sub_le _ _
    _ = lam * ‖B x - B y‖ + α * ‖x - y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlam,
          abs_of_nonneg hα0]
    _ ≤ lam * (L * ‖x - y‖) + α * ‖x - y‖ := by gcongr; exact hBL x y
    _ = _ := by ring

theorem coco_lip_aux (L t s ip : ℝ) (hL : 0 < L) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (h1 : L⁻¹ * t ^ 2 ≤ ip) (h2 : ip ≤ t * s) : t ≤ L * s := by
  have h3 : t ^ 2 ≤ L * (t * s) := by
    have := mul_le_mul_of_nonneg_left (h1.trans h2) hL.le
    rwa [← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul] at this
  by_contra hc
  push_neg at hc
  have : L * s * t < t * t := mul_lt_mul_of_pos_right hc (lt_of_le_of_lt (by positivity) hc)
  nlinarith

theorem coco_g_aux (lam α L t s ip : ℝ) (hlam : 0 < lam) (hα0 : 0 ≤ α) (hL : 0 < L)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (h1 : L⁻¹ * t ^ 2 ≤ ip) (hts : t ≤ L * s) :
    lam ^ 2 * t ^ 2 - 2 * lam * α * ip + α ^ 2 * s ^ 2 ≤ (max (lam * L - α) α * s) ^ 2 := by
  have hip : lam ^ 2 * t ^ 2 - 2 * lam * α * ip ≤ lam * L⁻¹ * (lam * L - 2 * α) * t ^ 2 := by
    have e : lam * L⁻¹ * (lam * L - 2 * α) * t ^ 2
        = lam ^ 2 * t ^ 2 - 2 * lam * α * (L⁻¹ * t ^ 2) := by
      field_simp
    rw [e]
    have : 0 ≤ 2 * lam * α := by positivity
    nlinarith
  have hLi : 0 < lam * L⁻¹ := by positivity
  rcases le_total (lam * L) (2 * α) with h | h
  · have : lam * L⁻¹ * (lam * L - 2 * α) * t ^ 2 ≤ 0 := by
      have : lam * L⁻¹ * (lam * L - 2 * α) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hLi.le (by linarith)
      exact mul_nonpos_of_nonpos_of_nonneg this (sq_nonneg t)
    have hm : α ≤ max (lam * L - α) α := le_max_right _ _
    have : α ^ 2 * s ^ 2 ≤ (max (lam * L - α) α * s) ^ 2 := by
      rw [mul_pow]; gcongr
    linarith
  · have hm : max (lam * L - α) α = lam * L - α := max_eq_left (by linarith)
    rw [hm]
    have ht2 : t ^ 2 ≤ (L * s) ^ 2 := by gcongr
    have hc : 0 ≤ lam * L⁻¹ * (lam * L - 2 * α) := mul_nonneg hLi.le (by linarith)
    have := mul_le_mul_of_nonneg_left ht2 hc
    have e : lam * L⁻¹ * (lam * L - 2 * α) * (L * s) ^ 2 + α ^ 2 * s ^ 2
        = ((lam * L - α) * s) ^ 2 := by
      field_simp
      ring
    nlinarith

theorem glip2 (B : H → H) (α lam L : ℝ) (hα0 : 0 ≤ α) (hlam : 0 < lam) (hL : 0 < L)
    (hco : ∀ x y, L⁻¹ * ‖B x - B y‖ ^ 2 ≤ inner ℝ (B x - B y) (x - y)) (x y : H) :
    ‖(lam • B x - α • x) - (lam • B y - α • y)‖ ≤ max (lam * L - α) α * ‖x - y‖ := by
  have e : (lam • B x - α • x) - (lam • B y - α • y) = lam • (B x - B y) - α • (x - y) := by
    module
  rw [e]
  have hts : ‖B x - B y‖ ≤ L * ‖x - y‖ :=
    coco_lip_aux L _ _ _ hL (norm_nonneg _) (norm_nonneg _) (hco x y)
      (real_inner_le_norm _ _)
  have hsq : ‖lam • (B x - B y) - α • (x - y)‖ ^ 2 ≤ (max (lam * L - α) α * ‖x - y‖) ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlam, abs_of_nonneg hα0]
    have := coco_g_aux lam α L _ _ _ hlam hα0 hL (norm_nonneg _) (norm_nonneg _) (hco x y) hts
    nlinarith
  have hK : 0 ≤ max (lam * L - α) α * ‖x - y‖ :=
    mul_nonneg (le_trans hα0 (le_max_right _ _)) (norm_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hK two_ne_zero).mp hsq

theorem coco_lip (B : H → H) (L : ℝ) (hL : 0 < L)
    (hco : ∀ x y, L⁻¹ * ‖B x - B y‖ ^ 2 ≤ inner ℝ (B x - B y) (x - y)) (x y : H) :
    ‖B x - B y‖ ≤ L * ‖x - y‖ :=
  coco_lip_aux L _ _ _ hL (norm_nonneg _) (norm_nonneg _) (hco x y) (real_inner_le_norm _ _)

end RRAux_FRBSplitting_Inertial_theorem_4_3

open RRAux_FRBSplitting_Inertial_theorem_4_3 in
open FRBSplitting.Inertial in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (L α β lam : ℝ)
    (hA : IsMaximalMonotone A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B)
    (hzer : (FRBSplitting.Weak.zeroSet A B).Nonempty)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hlam : 0 < lam) (hL : 0 < L)
    (hcase : (IsLipschitzOp L B ∧
        lam < min ((2 - β - α * β - 2 * α) / (2 * L)) ((1 - α - α * β) / (β * L))) ∨
      (IsCocoercive L⁻¹ B ∧ α < (2 - β) / (2 + β) ∧
        lam < min ((2 - β - α * β + 2 * α) / (2 * L)) ((1 - α + α * β) / (β * L))))
    (x z : ℕ → H) (hrun : IsRelaxedInertialRun J B α β lam x z) :
    ∃ xs ∈ FRBSplitting.Weak.zeroSet A B, FRBSplitting.Weak.IsWeakLimit x xs := by
  have hBL : ∀ x y, ‖B x - B y‖ ≤ L * ‖x - y‖ := by
    rcases hcase with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact coco_lip B L hL h
  obtain ⟨K, hK0, hG, hK1, hK2⟩ : ∃ K : ℝ, 0 ≤ K ∧
      (∀ x y, ‖(lam • B x - α • x) - (lam • B y - α • y)‖ ≤ K * ‖x - y‖) ∧
      2 * K < 2 - β - α * β ∧ K * β < 1 - α := by
    rcases hcase with ⟨hl, h⟩ | ⟨hc, h0, h⟩
    · rw [lt_min_iff] at h
      obtain ⟨a, b⟩ := params1 α β lam L hβ0 hlam hL h.1 h.2
      exact ⟨lam * L + α, by positivity, glip1 B α lam L hα0 hlam hl, a, b⟩
    · rw [lt_min_iff] at h
      obtain ⟨a, b⟩ := params2 α β lam L hα0 hβ0 hlam hL h0 h.1 h.2
      exact ⟨max (lam * L - α) α, le_trans hα0 (le_max_right _ _),
        glip2 B α lam L hα0 hlam hL hc, a, b⟩
  have hT : OpialKit.MaxMono (fun y => {w | ∃ a ∈ A y, w = a + B y}) :=
    OpialKit.maxMono_add_lipschitz hA J hJ hBm hL hBL
  have hcore : ∀ p ∈ FRBSplitting.Weak.zeroSet A B,
      (∃ r, Filter.Tendsto (fun n => ‖x n - p‖) Filter.atTop (nhds r)) ∧
      Filter.Tendsto (fun n => ‖x (n + 1) - x n‖) Filter.atTop (nhds 0) := fun p hp =>
    core A B J α β lam K x z p hA.1 hJ hBm hG hα1 hβ0 hβ1 hlam hK0 hK1 hK2 hrun hp
  obtain ⟨p, hp⟩ := hzer
  have hD := (hcore p hp).2
  obtain ⟨xs, hxs, hw⟩ := OpialKit.opial (FRBSplitting.Weak.zeroSet A B) ⟨p, hp⟩ x
    (fun q hq => (hcore q hq).1)
    (fun φ q hφ hq => cluster A B J α β lam L x z hT hJ hBL hL.le hα0 hβ0 hlam hrun hD φ hφ q hq)
  exact ⟨xs, hxs, hw⟩

#print axioms solution
