-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.hashimoto_multishift_unbounded_example
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:03:25.296086+00:00
-- url     : https://prove2.me/submissions/ef45bd4e-4fbd-49be-bd78-0a5e7522c409

/- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean
Supporting complete proofs from ChapterHashimotoShiftInvert.lean and
ChapterHermiteGalerkinFriedrichs.lean in the same revision. -/
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
import Definitions.Def_ChapterComplexShiftCore
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace BookProof.HashimotoShiftInvert
open BookProof.FarisLavine
open Filter Topology
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
@[simp] theorem shiftMap_apply (A : Dom →ₗ[ℂ] F) (γ : ℝ) (x : Dom) :
    shiftMap A γ x = A x + (γ : ℂ) • (x : F) := rfl

theorem norm_shiftMap_ge {A : Dom →ₗ[ℂ] F} (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    {γ : ℝ} (x : Dom) :
    γ * ‖(x : F)‖ ≤ ‖shiftMap A γ x‖ := by
  have hxy : (inner ℂ (x : F) (shiftMap A γ x) : ℂ).re = quadForm A x + γ * ‖(x : F)‖ ^ 2 := by
    simp only [shiftMap_apply, inner_add_right, inner_smul_right, Complex.add_re, quadForm]
    rw [inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have h1 : γ * ‖(x : F)‖ ^ 2 ≤ (inner ℂ (x : F) (shiftMap A γ x) : ℂ).re := by
    rw [hxy]; linarith [hpos x]
  have h2 : (inner ℂ (x : F) (shiftMap A γ x) : ℂ).re ≤ ‖(x : F)‖ * ‖shiftMap A γ x‖ :=
    le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)
  rcases eq_or_lt_of_le (norm_nonneg (x : F)) with h0 | hpx
  · rw [← h0]
    simp
  · nlinarith

theorem shiftMap_injective {A : Dom →ₗ[ℂ] F} (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    {γ : ℝ} (hγ : 0 < γ) : Function.Injective (shiftMap A γ) := by
  intro x y hxy
  have h : γ * ‖((x - y : Dom) : F)‖ ≤ ‖shiftMap A γ (x - y)‖ := norm_shiftMap_ge hpos _
  rw [map_sub, hxy, sub_self, norm_zero] at h
  have hx : ‖((x - y : Dom) : F)‖ = 0 := le_antisymm (by nlinarith) (norm_nonneg _)
  have : ((x - y : Dom) : F) = 0 := by simpa using hx
  have hz : x - y = 0 := Subtype.ext (by simpa using this)
  exact sub_eq_zero.mp hz

theorem IsShiftInvert.mem {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (u : F) : R u ∈ Dom := (h.2 u).choose

theorem IsShiftInvert.shift_apply {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (u : F) :
    A ⟨R u, h.mem u⟩ + (γ : ℂ) • R u = u := (h.2 u).choose_spec

theorem IsShiftInvert.isSelfAdjoint [CompleteSpace F] {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hsym : SymmetricOn Dom A) : IsSelfAdjoint R := by
  refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr ?_
  intro u v
  have hu : A ⟨R u, h.mem u⟩ + (γ : ℂ) • R u = u := h.shift_apply u
  have hv : A ⟨R v, h.mem v⟩ + (γ : ℂ) • R v = v := h.shift_apply v
  have hcross : (inner ℂ (A ⟨R u, h.mem u⟩) (R v) : ℂ)
      = inner ℂ (R u) (A ⟨R v, h.mem v⟩) := hsym ⟨R u, h.mem u⟩ ⟨R v, h.mem v⟩
  have e1 : (inner ℂ (R u) v : ℂ)
      = inner ℂ (R u) (A ⟨R v, h.mem v⟩) + (γ : ℂ) * inner ℂ (R u) (R v) := by
    conv_lhs => rw [← hv]
    rw [inner_add_right, inner_smul_right]
  have e2 : (inner ℂ u (R v) : ℂ)
      = inner ℂ (A ⟨R u, h.mem u⟩) (R v) + (γ : ℂ) * inner ℂ (R u) (R v) := by
    conv_lhs => rw [← hu]
    rw [inner_add_left, inner_smul_left]
    simp
  change (inner ℂ (R u) v : ℂ) = inner ℂ u (R v)
  rw [e1, e2, hcross]

theorem IsShiftInvert.dom_eq_range {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) : Dom = LinearMap.range (R : F →ₗ[ℂ] F) := by
  apply le_antisymm
  · intro x hx
    exact ⟨shiftMap A γ ⟨x, hx⟩, h.1 ⟨x, hx⟩⟩
  · rintro _ ⟨u, rfl⟩
    exact h.mem u

theorem exists_isShiftInvert {A : Dom →ₗ[ℂ] F} (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    {γ : ℝ} (hγ : 0 < γ) (hsurj : Function.Surjective (shiftMap A γ)) :
    ∃ R : F →L[ℂ] F, IsShiftInvert A γ R := by
  classical
  have hinj : Function.Injective (shiftMap A γ) := shiftMap_injective hpos hγ
  choose g hg using hsurj
  have hgshift : ∀ x : Dom, g (shiftMap A γ x) = x := fun x => hinj (hg _)
  have hadd : ∀ u v : F, ((g (u + v) : Dom) : F) = (g u : F) + (g v : F) := by
    intro u v
    have : shiftMap A γ (g (u + v)) = shiftMap A γ (g u + g v) := by
      rw [hg, map_add, hg, hg]
    exact congrArg Subtype.val (hinj this)
  have hsmul : ∀ (c : ℂ) (u : F), ((g (c • u) : Dom) : F) = c • (g u : F) := by
    intro c u
    have : shiftMap A γ (g (c • u)) = shiftMap A γ (c • g u) := by
      rw [hg, map_smul, hg]
    exact congrArg Subtype.val (hinj this)
  let L : F →ₗ[ℂ] F :=
    { toFun := fun u => (g u : F)
      map_add' := hadd
      map_smul' := by intro c u; simpa using hsmul c u }
  have hbound : ∀ u : F, ‖L u‖ ≤ γ⁻¹ * ‖u‖ := by
    intro u
    have hb : γ * ‖((g u : Dom) : F)‖ ≤ ‖shiftMap A γ (g u)‖ := norm_shiftMap_ge hpos _
    rw [hg u] at hb
    rw [inv_mul_eq_div, le_div_iff₀ hγ, mul_comm]
    exact hb
  refine ⟨L.mkContinuous γ⁻¹ hbound, fun x => ?_, fun u => ?_⟩
  · change ((g (shiftMap A γ x) : Dom) : F) = (x : F)
    rw [hgshift x]
  · refine ⟨(g u).2, ?_⟩
    have hsub : (⟨((g u : Dom) : F), (g u).2⟩ : Dom) = g u := Subtype.ext rfl
    change shiftMap A γ ⟨((g u : Dom) : F), _⟩ = u
    rw [hsub, hg u]
section Complete
variable [CompleteSpace F]
theorem shiftRange_isClosed {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A)
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    (hsa : ∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)
    {γ : ℝ} (hγ : 0 < γ) : IsClosed ((shiftRange A γ : Submodule ℂ F) : Set F) := by
  refine IsSeqClosed.isClosed ?_
  intro u p hu hup
  choose x hx using hu
  -- the preimages form a Cauchy sequence, by the shift bound
  have hcauchy : CauchySeq (fun n => ((x n : F))) := by
    have hucauchy : CauchySeq u := hup.cauchySeq
    rw [Metric.cauchySeq_iff] at hucauchy ⊢
    intro eps heps
    obtain ⟨N, hN⟩ := hucauchy (γ * eps) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hb : γ * ‖((x m - x n : Dom) : F)‖ ≤ ‖shiftMap A γ (x m - x n)‖ :=
      norm_shiftMap_ge hpos _
    rw [map_sub, hx m, hx n] at hb
    have hlt : ‖u m - u n‖ < γ * eps := by
      have hd := hN m hm n hn
      rwa [dist_eq_norm] at hd
    have hkey : γ * ‖((x m : F)) - ((x n : F))‖ < γ * eps := by
      refine lt_of_le_of_lt ?_ hlt
      simpa using hb
    rw [dist_eq_norm]
    exact lt_of_mul_lt_mul_left hkey hγ.le
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- and their images under `A` converge too
  have hAconv : Tendsto (fun n => A (x n)) atTop (nhds (p - (γ : ℂ) • w)) := by
    have hval : ∀ n, A (x n) = u n - (γ : ℂ) • ((x n : F)) := by
      intro n
      have hn := hx n
      simp only [shiftMap_apply] at hn
      exact eq_sub_of_add_eq hn
    simp only [hval]
    exact hup.sub (hw.const_smul ((γ : ℂ)))
  obtain ⟨hwmem, hAw⟩ := closed_of_selfAdjointCriterion hsym hsa hw hAconv
  refine ⟨⟨w, hwmem⟩, ?_⟩
  simp only [shiftMap_apply, hAw]
  abel

theorem shiftRange_orthogonal_eq_bot {A : Dom →ₗ[ℂ] F}
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    (hsa : ∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)
    {γ : ℝ} (hγ : 0 < γ) : (shiftRange A γ)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  have hip : ∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) (-(γ : ℂ) • w) := by
    intro v
    have hmem : shiftMap A γ v ∈ shiftRange A γ := ⟨v, rfl⟩
    have h0 : (inner ℂ (shiftMap A γ v) w : ℂ) = 0 := hw _ hmem
    rw [shiftMap_apply, inner_add_left, inner_smul_left, Complex.conj_ofReal] at h0
    rw [inner_smul_right]
    have hval : (inner ℂ (A v) w : ℂ) = -((γ : ℂ) * inner ℂ ((v : F)) w) := by
      linear_combination h0
    rw [hval]
    ring
  obtain ⟨hwmem, hAw⟩ := hsa w (-(γ : ℂ) • w) hip
  have hquad : quadForm A ⟨w, hwmem⟩ = -γ * ‖w‖ ^ 2 := by
    rw [quadForm, hAw, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have h1 := hpos ⟨w, hwmem⟩
  rw [hquad] at h1
  have hzero : ‖w‖ = 0 := by
    by_contra hne
    have hpw : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hne)
    have hcontr : 0 < γ * ‖w‖ ^ 2 := by positivity
    linarith
  simpa using hzero

theorem shiftMap_surjective {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A)
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    (hsa : ∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)
    {γ : ℝ} (hγ : 0 < γ) : Function.Surjective (shiftMap A γ) := by
  have hclosed : IsClosed ((shiftRange A γ : Submodule ℂ F) : Set F) :=
    shiftRange_isClosed hsym hpos hsa hγ
  haveI : CompleteSpace (shiftRange A γ) := hclosed.completeSpace_coe
  have htop : shiftRange A γ = ⊤ := by
    have h1 := Submodule.orthogonal_orthogonal (shiftRange A γ)
    rw [shiftRange_orthogonal_eq_bot hpos hsa hγ, Submodule.bot_orthogonal_eq_top] at h1
    exact h1.symm
  intro u
  have hmem : u ∈ shiftRange A γ := by rw [htop]; trivial
  exact hmem

end Complete
end BookProof.HashimotoShiftInvert
namespace BookProof.ChapterH9
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem norm_sub_starProjection_le (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (u w : E) (hw : w ∈ K) : ‖u - K.starProjection u‖ ≤ ‖u - w‖ := by
  rw [Submodule.starProjection_minimal]
  refine ciInf_le_of_le ⟨0, ?_⟩ (⟨w, hw⟩ : K) le_rfl
  rintro r ⟨x, rfl⟩
  positivity

end BookProof.ChapterH9
namespace BookProof.HermiteGalerkin
open Filter Topology
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
theorem starProjection_tendsto_of_monotone_dense (K : ℕ → Submodule ℂ F)
    [∀ n, (K n).HasOrthogonalProjection] (hmono : Monotone K)
    (hdense : Dense ((⨆ n : ℕ, K n : Submodule ℂ F) : Set F)) (u : F) :
    Tendsto (fun n : ℕ => (K n).starProjection u) atTop (nhds u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨w, hw, hwd⟩ := hdense.exists_dist_lt u heps
  obtain ⟨N, hN⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hw
  refine ⟨N, fun n hn => ?_⟩
  have h1 : ‖u - (K n).starProjection u‖ ≤ ‖u - w‖ :=
    BookProof.ChapterH9.norm_sub_starProjection_le _ u w (hmono hn hN)
  have h2 : ‖u - w‖ < eps := by simpa [dist_eq_norm] using hwd
  have h3 : ‖(K n).starProjection u - u‖ = ‖u - (K n).starProjection u‖ := norm_sub_rev _ _
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), h3]
  exact lt_of_le_of_lt h1 h2

theorem compression_tendsto_of_starProjection_tendsto (K : ℕ → Submodule ℂ F)
    [∀ n, (K n).HasOrthogonalProjection] (A : F →L[ℂ] F)
    (hP : ∀ u : F, Tendsto (fun n : ℕ => (K n).starProjection u) atTop (nhds u)) (u : F) :
    Tendsto (fun n : ℕ => (K n).starProjection (A ((K n).starProjection u)))
      atTop (nhds (A u)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ n : ℕ, ‖(K n).starProjection (A ((K n).starProjection u)) - A u‖
      ≤ ‖A‖ * ‖(K n).starProjection u - u‖ + ‖(K n).starProjection (A u) - A u‖ := by
    intro n
    have hsplit : (K n).starProjection (A ((K n).starProjection u)) - A u
        = (K n).starProjection (A ((K n).starProjection u) - A u)
          + ((K n).starProjection (A u) - A u) := by
      simp only [map_sub]
      abel
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    gcongr
    refine le_trans ((K n).norm_starProjection_apply_le _) ?_
    have hAsub : A ((K n).starProjection u) - A u = A ((K n).starProjection u - u) := by
      rw [map_sub]
    rw [hAsub]
    exact A.le_opNorm _
  have h1 : Tendsto (fun n : ℕ => ‖A‖ * ‖(K n).starProjection u - u‖) atTop (nhds 0) := by
    have := hP u
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    simpa using this.const_mul ‖A‖
  have h2 : Tendsto (fun n : ℕ => ‖(K n).starProjection (A u) - A u‖) atTop (nhds 0) := by
    have := hP (A u)
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    simpa using this
  exact squeeze_zero (fun n => norm_nonneg _) hbound (by simpa using h1.add h2)

theorem galerkinSpan_mono (b : HilbertBasis ℕ ℂ F) {m n : ℕ} (hmn : m ≤ n) :
    galerkinSpan b m ≤ galerkinSpan b n :=
  Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi hmn)

theorem basis_mem_galerkinSpan (b : HilbertBasis ℕ ℂ F) {i m : ℕ} (him : i < m) :
    b i ∈ galerkinSpan b m :=
  Submodule.subset_span ⟨i, him, rfl⟩

theorem galerkinSpan_le_finiteModeDomain (b : HilbertBasis ℕ ℂ F) (m : ℕ) :
    galerkinSpan b m ≤ finiteModeDomain b :=
  Submodule.span_mono (by rintro x ⟨i, _, rfl⟩; exact ⟨i, rfl⟩)

theorem finiteModeDomain_eq_iSup (b : HilbertBasis ℕ ℂ F) :
    finiteModeDomain b = ⨆ m : ℕ, galerkinSpan b m := by
  refine le_antisymm ?_ (iSup_le fun m => galerkinSpan_le_finiteModeDomain b m)
  rw [finiteModeDomain, Submodule.span_le]
  rintro x ⟨i, rfl⟩
  exact Submodule.mem_iSup_of_mem (i + 1) (basis_mem_galerkinSpan b (Nat.lt_succ_self i))

theorem exists_mem_galerkinSpan (b : HilbertBasis ℕ ℂ F) {x : F} (hx : x ∈ finiteModeDomain b) :
    ∃ m : ℕ, x ∈ galerkinSpan b m := by
  rw [finiteModeDomain_eq_iSup] at hx
  have hmono : Monotone (fun m : ℕ => galerkinSpan b m) := fun _ _ h => galerkinSpan_mono b h
  have hdir : Directed (· ≤ ·) (fun m : ℕ => galerkinSpan b m) := hmono.directed_le
  exact (Submodule.mem_iSup_of_directed _ hdir).mp hx

theorem finiteModeDomain_dense (b : HilbertBasis ℕ ℂ F) :
    Dense ((finiteModeDomain b : Submodule ℂ F) : Set F) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span

theorem galerkinSpan_iSup_dense (b : HilbertBasis ℕ ℂ F) :
    Dense ((⨆ m : ℕ, galerkinSpan b m : Submodule ℂ F) : Set F) := by
  rw [← finiteModeDomain_eq_iSup]
  exact finiteModeDomain_dense b

theorem galerkinProj_tendsto (b : HilbertBasis ℕ ℂ F) (u : F) :
    Tendsto (fun m : ℕ => (galerkinSpan b m).starProjection u) atTop (nhds u) :=
  starProjection_tendsto_of_monotone_dense _ (fun _ _ h => galerkinSpan_mono b h)
    (galerkinSpan_iSup_dense b) u

@[simp] theorem galerkinCompression_apply (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (m : ℕ)
    (u : F) : galerkinCompression A b m u
      = (galerkinSpan b m).starProjection (A ((galerkinSpan b m).starProjection u)) := rfl

theorem galerkinCompression_tendsto (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (u : F) :
    Tendsto (fun m : ℕ => galerkinCompression A b m u) atTop (nhds (A u)) :=
  compression_tendsto_of_starProjection_tendsto _ A (galerkinProj_tendsto b) u
end BookProof.HermiteGalerkin

namespace BookProof.HermiteGalerkin
open Filter Topology
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
theorem norm_sub_smul_ge (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) (z : ℂ) (u : F) :
    |z.im| * ‖u‖ ≤ ‖(algebraMap ℂ (F →L[ℂ] F) z - T) u‖ := by
  have h : (inner ℂ (T u) u : ℂ) = inner ℂ u (T u) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT) u u
  have hsym : (inner ℂ u (T u) : ℂ).im = 0 := by
    refine Complex.conj_eq_iff_im.mp ?_
    rw [inner_conj_symm]
    exact h
  have happ : (algebraMap ℂ (F →L[ℂ] F) z - T) u = z • u - T u := by
    simp [Algebra.algebraMap_eq_smul_one]
  have hinner : (inner ℂ u ((algebraMap ℂ (F →L[ℂ] F) z - T) u) : ℂ).im = z.im * ‖u‖ ^ 2 := by
    rw [happ, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.sub_im,
      hsym, sub_zero, Complex.mul_im]
    simp [← Complex.ofReal_pow]
  have hcs : |(inner ℂ u ((algebraMap ℂ (F →L[ℂ] F) z - T) u) : ℂ).im|
      ≤ ‖u‖ * ‖(algebraMap ℂ (F →L[ℂ] F) z - T) u‖ :=
    le_trans (Complex.abs_im_le_norm _) (norm_inner_le_norm _ _)
  rw [hinner] at hcs
  rcases eq_or_lt_of_le (norm_nonneg u) with h0 | hpos
  · simp [← h0]
  · rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖u‖ ^ 2)] at hcs
    nlinarith [hcs, hpos]

theorem isUnit_algebraMap_sub (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) {z : ℂ} (hz : z.im ≠ 0) :
    IsUnit (algebraMap ℂ (F →L[ℂ] F) z - T) := by
  have hspec : z ∉ spectrum ℂ T := by
    intro hmem
    exact hz (by rw [← hT.spectrumRestricts.rightInvOn hmem]; simp)
  simpa [spectrum.mem_iff] using hspec

theorem sub_resolvent_apply (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) {z : ℂ} (hz : z.im ≠ 0)
    (w : F) : (algebraMap ℂ (F →L[ℂ] F) z - T) (resolvent T z w) = w := by
  have hmul : (algebraMap ℂ (F →L[ℂ] F) z - T) * resolvent T z = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_algebraMap_sub T hT hz)
  calc (algebraMap ℂ (F →L[ℂ] F) z - T) (resolvent T z w)
      = ((algebraMap ℂ (F →L[ℂ] F) z - T) * resolvent T z) w := rfl
    _ = w := by rw [hmul]; rfl

theorem norm_resolvent_apply_le (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) {z : ℂ} (hz : z.im ≠ 0)
    (w : F) : |z.im| * ‖resolvent T z w‖ ≤ ‖w‖ := by
  have h := norm_sub_smul_ge T hT z (resolvent T z w)
  rwa [sub_resolvent_apply T hT hz w] at h

theorem resolvent_tendsto_of_strong_tendsto (T : ℕ → F →L[ℂ] F) (A : F →L[ℂ] F)
    (hT : ∀ n, IsSelfAdjoint (T n)) (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0)
    (hconv : ∀ u : F, Tendsto (fun n : ℕ => T n u) atTop (nhds (A u))) (u : F) :
    Tendsto (fun n : ℕ => resolvent (T n) z u) atTop (nhds (resolvent A z u)) := by
  have hzpos : 0 < |z.im| := abs_pos.mpr hz
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ n : ℕ, ‖resolvent (T n) z u - resolvent A z u‖
      ≤ ‖T n (resolvent A z u) - A (resolvent A z u)‖ / |z.im| := by
    intro n
    have hSn : resolvent (T n) z * (algebraMap ℂ (F →L[ℂ] F) z - T n) = 1 :=
      Ring.inverse_mul_cancel _ (isUnit_algebraMap_sub (T n) (hT n) hz)
    have hS : (algebraMap ℂ (F →L[ℂ] F) z - A) * resolvent A z = 1 :=
      Ring.mul_inverse_cancel _ (isUnit_algebraMap_sub A hA hz)
    have hsub : (T n - A)
        = (algebraMap ℂ (F →L[ℂ] F) z - A) - (algebraMap ℂ (F →L[ℂ] F) z - T n) := by abel
    have hid : resolvent (T n) z - resolvent A z
        = resolvent (T n) z * (T n - A) * resolvent A z := by
      rw [hsub, mul_sub, sub_mul, mul_assoc, hS, hSn]
      simp
    have happ : resolvent (T n) z u - resolvent A z u
        = resolvent (T n) z (T n (resolvent A z u) - A (resolvent A z u)) := by
      have := congrArg (fun S : F →L[ℂ] F => S u) hid
      simpa using this
    rw [happ, le_div_iff₀ hzpos, mul_comm]
    exact norm_resolvent_apply_le (T n) (hT n) hz _
  have hconv0 : Tendsto
      (fun n : ℕ => ‖T n (resolvent A z u) - A (resolvent A z u)‖ / |z.im|) atTop (nhds 0) := by
    have h := hconv (resolvent A z u)
    rw [tendsto_iff_norm_sub_tendsto_zero] at h
    simpa using h.div_const |z.im|
  exact squeeze_zero (fun n => norm_nonneg _) hbound hconv0

theorem isSelfAdjoint_galerkinCompression {A : F →L[ℂ] F} (hA : IsSelfAdjoint A)
    (b : HilbertBasis ℕ ℂ F) (m : ℕ) : IsSelfAdjoint (galerkinCompression A b m) := by
  have hP : IsSelfAdjoint (galerkinSpan b m).starProjection :=
    isSelfAdjoint_starProjection _
  change star ((galerkinSpan b m).starProjection * A * (galerkinSpan b m).starProjection)
    = (galerkinSpan b m).starProjection * A * (galerkinSpan b m).starProjection
  rw [star_mul, star_mul, hP.star_eq, hA.star_eq, mul_assoc]

theorem galerkinResolvent_tendsto {A : F →L[ℂ] F} (hA : IsSelfAdjoint A)
    (b : HilbertBasis ℕ ℂ F) {z : ℂ} (hz : z.im ≠ 0) (u : F) :
    Tendsto (fun m : ℕ => resolvent (galerkinCompression A b m) z u) atTop
      (nhds (resolvent A z u)) :=
  resolvent_tendsto_of_strong_tendsto _ A (fun m => isSelfAdjoint_galerkinCompression hA b m) hA
    hz (galerkinCompression_tendsto A b) u
end BookProof.HermiteGalerkin

namespace BookProof.HashimotoShiftInvert
open Filter Topology
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {Dom : Submodule ℂ F}
theorem IsShiftInvert.apply_eq {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (u : F) :
    A ⟨R u, h.mem u⟩ = u - (γ : ℂ) • R u :=
  eq_sub_of_add_eq (h.shift_apply u)

theorem IsShiftInvert.norm_apply_le {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ) (u : F) :
    ‖R u‖ ≤ γ⁻¹ * ‖u‖ := by
  have hb : γ * ‖((⟨R u, h.mem u⟩ : Dom) : F)‖ ≤ ‖shiftMap A γ ⟨R u, h.mem u⟩‖ :=
    norm_shiftMap_ge hpos _
  rw [show shiftMap A γ ⟨R u, h.mem u⟩ = u from h.shift_apply u] at hb
  rw [inv_mul_eq_div, le_div_iff₀ hγ, mul_comm]
  simpa using hb

theorem IsShiftInvert.opNorm_le {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ) :
    ‖R‖ ≤ γ⁻¹ :=
  R.opNorm_le_bound (by positivity) (h.norm_apply_le hpos hγ)

theorem IsShiftInvert.inner_nonneg {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ) (u : F) :
    0 ≤ (inner ℂ u (R u) : ℂ).re := by
  have hu : A ⟨R u, h.mem u⟩ + (γ : ℂ) • R u = u := h.shift_apply u
  have key : ∀ (y : F) (hy : y ∈ Dom),
      (inner ℂ (A ⟨y, hy⟩ + (γ : ℂ) • y) y : ℂ).re = quadForm A ⟨y, hy⟩ + γ * ‖y‖ ^ 2 := by
    intro y hy
    have hq : (inner ℂ (A ⟨y, hy⟩) y : ℂ).re = quadForm A ⟨y, hy⟩ := by
      rw [quadForm, ← inner_conj_symm (A ⟨y, hy⟩) y, Complex.conj_re]
    rw [inner_add_left, inner_smul_left, Complex.add_re, hq, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hexp := key (R u) (h.mem u)
  rw [hu] at hexp
  rw [hexp]
  have := hpos ⟨R u, h.mem u⟩
  positivity

theorem shiftInvert_determines {Dom₁ Dom₂ : Submodule ℂ F} {A₁ : Dom₁ →ₗ[ℂ] F}
    {A₂ : Dom₂ →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h₁ : IsShiftInvert A₁ γ R) (h₂ : IsShiftInvert A₂ γ R) :
    Dom₁ = Dom₂ ∧ ∀ (x : F) (hx₁ : x ∈ Dom₁) (hx₂ : x ∈ Dom₂), A₁ ⟨x, hx₁⟩ = A₂ ⟨x, hx₂⟩ := by
  refine ⟨by rw [h₁.dom_eq_range, h₂.dom_eq_range], ?_⟩
  intro x hx₁ hx₂
  set u : F := shiftMap A₁ γ ⟨x, hx₁⟩ with hu
  have hRu : R u = x := h₁.1 ⟨x, hx₁⟩
  have e₁ : A₁ ⟨R u, h₁.mem u⟩ = u - (γ : ℂ) • R u := h₁.apply_eq u
  have e₂ : A₂ ⟨R u, h₂.mem u⟩ = u - (γ : ℂ) • R u := h₂.apply_eq u
  have c₁ : (⟨R u, h₁.mem u⟩ : Dom₁) = ⟨x, hx₁⟩ := Subtype.ext hRu
  have c₂ : (⟨R u, h₂.mem u⟩ : Dom₂) = ⟨x, hx₂⟩ := Subtype.ext hRu
  rw [c₁] at e₁
  rw [c₂] at e₂
  rw [e₁, e₂]

theorem hashimoto_shiftInvert_selects_friedrichs (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) {Dom : Submodule ℂ F} (A : Dom →ₗ[ℂ] F)
    (hA : IsPositiveSelfAdjointExtension H A) {γ : ℝ} (hγ : 0 < γ) :
    ∃ R : F →L[ℂ] F,
      IsShiftInvert A γ R ∧ ‖R‖ ≤ γ⁻¹ ∧ IsSelfAdjoint R ∧
      (∀ u : F, 0 ≤ (inner ℂ u (R u) : ℂ).re) ∧
      (∀ u : F, Tendsto (fun m : ℕ => galerkinCompression R b m u) atTop (nhds (R u))) ∧
      (∀ z : ℂ, z.im ≠ 0 → ∀ u : F,
        Tendsto (fun m : ℕ => resolvent (galerkinCompression R b m) z u) atTop
          (nhds (resolvent R z u))) ∧
      (∀ (Dom' : Submodule ℂ F) (A' : Dom' →ₗ[ℂ] F), IsShiftInvert A' γ R →
        Dom' = Dom ∧ ∀ (x : F) (hx : x ∈ Dom) (hx' : x ∈ Dom'), A' ⟨x, hx'⟩ = A ⟨x, hx⟩) := by
  obtain ⟨-, hsym, hpos, hsa⟩ := hA
  obtain ⟨R, hR⟩ := exists_isShiftInvert hpos hγ (shiftMap_surjective hsym hpos hsa hγ)
  have hRsa : IsSelfAdjoint R := hR.isSelfAdjoint hsym
  refine ⟨R, hR, hR.opNorm_le hpos hγ, hRsa, hR.inner_nonneg hpos hγ,
    fun u => galerkinCompression_tendsto R b u,
    fun z hz u => galerkinResolvent_tendsto hRsa b hz u, ?_⟩
  intro Dom' A' hA'
  obtain ⟨hdom, hval⟩ := shiftInvert_determines hA' hR
  exact ⟨hdom, fun x hx hx' => hval x hx' hx⟩
end BookProof.HashimotoShiftInvert

namespace BookProof.HashimotoShiftInvert
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology
open scoped InnerProductSpace ENNReal lp
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {Dom : Submodule ℂ F}
theorem IsShiftInvert.injective {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) : Function.Injective R := by
  intro u v huv
  have hu : A ⟨R u, h.mem u⟩ + (γ : ℂ) • R u = u := h.shift_apply u
  have hv : A ⟨R v, h.mem v⟩ + (γ : ℂ) • R v = v := h.shift_apply v
  have hsub : (⟨R u, h.mem u⟩ : Dom) = ⟨R v, h.mem v⟩ := Subtype.ext huv
  rw [← hu, ← hv, hsub, huv]

theorem preim_eq (R : F →L[ℂ] F) (hinj : Function.Injective R)
    (y : LinearMap.range (R : F →ₗ[ℂ] F)) {u : F} (hu : R u = (y : F)) : preim R y = u :=
  hinj (by rw [preim_spec, hu])

@[simp] theorem invShiftOperator_apply (R : F →L[ℂ] F) (hinj : Function.Injective R) (γ : ℝ)
    (y : LinearMap.range (R : F →ₗ[ℂ] F)) :
    invShiftOperator R hinj γ y = preim R y - (γ : ℂ) • (y : F) := rfl

theorem isShiftInvert_invShiftOperator (R : F →L[ℂ] F) (hinj : Function.Injective R) (γ : ℝ) :
    IsShiftInvert (invShiftOperator R hinj γ) γ R := by
  constructor
  · intro x
    have hx : shiftMap (invShiftOperator R hinj γ) γ x = preim R x := by
      simp [shiftMap_apply]
    rw [hx, preim_spec]
  · intro u
    refine ⟨⟨u, rfl⟩, ?_⟩
    have hpre : preim R ⟨R u, ⟨u, rfl⟩⟩ = u := preim_eq R hinj _ rfl
    simp [shiftMap_apply, hpre]

theorem invShiftOperator_symmetricOn (R : F →L[ℂ] F) (hinj : Function.Injective R) (γ : ℝ)
    (hR : IsSelfAdjoint R) :
    SymmetricOn (LinearMap.range (R : F →ₗ[ℂ] F)) (invShiftOperator R hinj γ) := by
  have hRsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hR
  intro y z
  have hy : R (preim R y) = (y : F) := preim_spec R y
  have hz : R (preim R z) = (z : F) := preim_spec R z
  have hcross : (inner ℂ (preim R y) (z : F) : ℂ) = inner ℂ (y : F) (preim R z) := by
    rw [← hy, ← hz]
    exact (hRsym (preim R y) (preim R z)).symm
  simp only [invShiftOperator_apply, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal, hcross]

theorem invShiftOperator_quadForm_nonneg (R : F →L[ℂ] F) (hinj : Function.Injective R) (γ : ℝ)
    (hposR : ∀ u : F, γ * ‖R u‖ ^ 2 ≤ (inner ℂ (R u) u : ℂ).re)
    (y : LinearMap.range (R : F →ₗ[ℂ] F)) : 0 ≤ quadForm (invShiftOperator R hinj γ) y := by
  have hy : R (preim R y) = (y : F) := preim_spec R y
  have hq : quadForm (invShiftOperator R hinj γ) y
      = (inner ℂ (y : F) (preim R y) : ℂ).re - γ * ‖(y : F)‖ ^ 2 := by
    rw [quadForm, invShiftOperator_apply, inner_sub_right, inner_smul_right, Complex.sub_re,
      inner_self_eq_norm_sq_to_K]
    congr 1
    simp [← Complex.ofReal_pow]
  have hp := hposR (preim R y)
  rw [hy] at hp
  rw [hq]
  linarith

theorem invShiftOperator_selfAdjointCriterion (R : F →L[ℂ] F) (hinj : Function.Injective R)
    (γ : ℝ) (hR : IsSelfAdjoint R) (w u : F)
    (hw : ∀ v : LinearMap.range (R : F →ₗ[ℂ] F),
      (inner ℂ (invShiftOperator R hinj γ v) w : ℂ) = inner ℂ (v : F) u) :
    ∃ h : w ∈ LinearMap.range (R : F →ₗ[ℂ] F), invShiftOperator R hinj γ ⟨w, h⟩ = u := by
  have hRsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hR
  have hkey : ∀ z : F, (inner ℂ z (w - (γ : ℂ) • R w - R u) : ℂ) = 0 := by
    intro z
    have hv := hw ⟨R z, ⟨z, rfl⟩⟩
    have hpre : preim R ⟨R z, ⟨z, rfl⟩⟩ = z := preim_eq R hinj _ rfl
    rw [invShiftOperator_apply, hpre] at hv
    have h1 : (inner ℂ (R z) w : ℂ) = inner ℂ z (R w) := hRsym z w
    have h2 : (inner ℂ (R z) u : ℂ) = inner ℂ z (R u) := hRsym z u
    rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal, h1, h2] at hv
    rw [inner_sub_right, inner_sub_right, inner_smul_right]
    rw [hv]
    ring
  have hzero : w - (γ : ℂ) • R w - R u = 0 :=
    inner_self_eq_zero.mp (hkey (w - (γ : ℂ) • R w - R u))
  have hwsum : w = (γ : ℂ) • R w + R u := by
    linear_combination (norm := module) hzero
  have hwval : w = R (u + (γ : ℂ) • w) := by
    rw [map_add, map_smul]
    linear_combination (norm := module) hwsum
  refine ⟨⟨u + (γ : ℂ) • w, hwval.symm⟩, ?_⟩
  have hpre : preim R ⟨w, ⟨u + (γ : ℂ) • w, hwval.symm⟩⟩ = u + (γ : ℂ) • w :=
    preim_eq R hinj _ hwval.symm
  rw [invShiftOperator_apply, hpre]
  module

theorem invShiftOperator_isPositiveSelfAdjointExtension (R : F →L[ℂ] F)
    (hinj : Function.Injective R) (γ : ℝ) (hR : IsSelfAdjoint R)
    (hposR : ∀ u : F, γ * ‖R u‖ ^ 2 ≤ (inner ℂ (R u) u : ℂ).re)
    {D : Submodule ℂ F} (hD : D ≤ LinearMap.range (R : F →ₗ[ℂ] F)) (H : D →ₗ[ℂ] F)
    (hH : ∀ x : D, H x = invShiftOperator R hinj γ ⟨(x : F), hD x.2⟩) :
    IsPositiveSelfAdjointExtension H (invShiftOperator R hinj γ) :=
  ⟨fun x => ⟨hD x.2, (hH x).symm⟩, invShiftOperator_symmetricOn R hinj γ hR,
    invShiftOperator_quadForm_nonneg R hinj γ hposR,
    invShiftOperator_selfAdjointCriterion R hinj γ hR⟩

theorem diagCLM_norm_apply_le {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) (x : ℓ²(ℕ, ℂ)) :
    ‖diagCLM hc x‖ ≤ ‖x‖ := diagLin_norm_le hc x

theorem diagCLM_symmetric {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) (x y : ℓ²(ℕ, ℂ)) :
    (inner ℂ (diagCLM hc x) y : ℂ) = inner ℂ x (diagCLM hc y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1
  funext n
  rw [diagCLM_apply, diagCLM_apply]
  simp [RCLike.inner_apply, map_mul]
  ring

theorem diagCLM_isSelfAdjoint {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) :
    IsSelfAdjoint (diagCLM hc) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (diagCLM_symmetric hc)

theorem ell2ShiftInvert_isSelfAdjoint : IsSelfAdjoint ell2ShiftInvert :=
  diagCLM_isSelfAdjoint invCoeff_abs_le_one

theorem sqrtInvCoeff_abs_le_one (n : ℕ) : |sqrtInvCoeff n| ≤ 1 := by
  have h0 : 0 ≤ sqrtInvCoeff n := Real.sqrt_nonneg _
  rw [abs_of_nonneg h0, sqrtInvCoeff]
  rw [show (1:ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (invCoeff_le_one n)

theorem ell2ShiftInvert_eq_sq (x : ℓ²(ℕ, ℂ)) :
    ell2ShiftInvert x = diagCLM sqrtInvCoeff_abs_le_one (diagCLM sqrtInvCoeff_abs_le_one x) := by
  apply lp.ext
  funext n
  rw [ell2ShiftInvert, diagCLM_apply, diagCLM_apply, diagCLM_apply, ← mul_assoc]
  congr 1
  rw [← Complex.ofReal_mul]
  norm_cast
  rw [sqrtInvCoeff, Real.mul_self_sqrt (invCoeff_pos n).le]

theorem ell2ShiftInvert_le_one (v : ℓ²(ℕ, ℂ)) :
    (1 : ℝ) * ‖ell2ShiftInvert v‖ ^ 2 ≤ (inner ℂ (ell2ShiftInvert v) v : ℂ).re := by
  set S := diagCLM sqrtInvCoeff_abs_le_one with hS
  have hsq : ell2ShiftInvert v = S (S v) := ell2ShiftInvert_eq_sq v
  have hinner : (inner ℂ (ell2ShiftInvert v) v : ℂ) = inner ℂ (S v) (S v) := by
    rw [hsq]
    exact diagCLM_symmetric sqrtInvCoeff_abs_le_one (S v) v
  have hre : (inner ℂ (ell2ShiftInvert v) v : ℂ).re = ‖S v‖ ^ 2 := by
    rw [hinner, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hnorm : ‖ell2ShiftInvert v‖ ≤ ‖S v‖ := by
    rw [hsq]
    exact diagCLM_norm_apply_le sqrtInvCoeff_abs_le_one (S v)
  rw [hre, one_mul]
  nlinarith [norm_nonneg (ell2ShiftInvert v), norm_nonneg (S v)]

theorem ell2UnboundedExample_isShiftInvert :
    IsShiftInvert ell2UnboundedExample 1 ell2ShiftInvert :=
  isShiftInvert_invShiftOperator ell2ShiftInvert ell2ShiftInvert_injective 1

theorem ell2Example_isPositiveSelfAdjointExtension :
    IsPositiveSelfAdjointExtension ell2ExampleMatrix ell2UnboundedExample :=
  invShiftOperator_isPositiveSelfAdjointExtension ell2ShiftInvert ell2ShiftInvert_injective 1
    ell2ShiftInvert_isSelfAdjoint ell2ShiftInvert_le_one finiteModeDomain_le_range
    ell2ExampleMatrix (fun _ => rfl)

theorem norm_single_one (k : ℕ) : ‖(lp.single 2 k (1 : ℂ) : ℓ²(ℕ, ℂ))‖ = 1 := by
  rw [lp.norm_single (by norm_num)]
  simp

theorem ell2ExampleMatrix_unbounded (C : ℝ) :
    ∃ x : finiteModeDomain ell2Basis, C * ‖(x : ℓ²(ℕ, ℂ))‖ < ‖ell2ExampleMatrix x‖ := by
  obtain ⟨k, hk⟩ := exists_nat_gt C
  have hmem : (lp.single 2 k (1 : ℂ) : ℓ²(ℕ, ℂ)) ∈ finiteModeDomain ell2Basis := by
    rw [← ell2Basis_apply]
    exact Submodule.subset_span ⟨k, rfl⟩
  refine ⟨⟨lp.single 2 k (1 : ℂ), hmem⟩, ?_⟩
  have hrange : (lp.single 2 k (1 : ℂ) : ℓ²(ℕ, ℂ))
      ∈ LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ)) :=
    finiteModeDomain_le_range hmem
  have hpre : preim ell2ShiftInvert ⟨lp.single 2 k (1 : ℂ), hrange⟩
      = ((k : ℂ) + 1) • lp.single 2 k (1 : ℂ) :=
    preim_eq _ ell2ShiftInvert_injective _ (ell2ShiftInvert_smul_single k)
  have hval : ell2ExampleMatrix ⟨lp.single 2 k (1 : ℂ), hmem⟩
      = (k : ℂ) • lp.single 2 k (1 : ℂ) := by
    change ell2UnboundedExample ⟨lp.single 2 k (1 : ℂ), hrange⟩ = _
    rw [ell2UnboundedExample, invShiftOperator_apply, hpre]
    push_cast
    module
  rw [hval, norm_smul, norm_single_one]
  simp only [mul_one, Complex.norm_natCast]
  exact hk
end BookProof.HashimotoShiftInvert

namespace BookProof.HashimotoShiftInvert
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology
open scoped InnerProductSpace ENNReal lp
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
theorem IsShiftInvertC.mem {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (u : F) : X u ∈ Dom := (h.2 u).choose

theorem IsShiftInvertC.shift_apply {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (u : F) :
    γ • X u - A ⟨X u, h.mem u⟩ = u := (h.2 u).choose_spec

theorem IsShiftInvertC.apply_eq {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (u : F) :
    A ⟨X u, h.mem u⟩ = γ • X u - u := by
  have h1 : γ • X u - A ⟨X u, h.mem u⟩ = u := h.shift_apply u
  have ha : γ • X u = u + A ⟨X u, h.mem u⟩ := sub_eq_iff_eq_add.mp h1
  rw [ha]; abel

theorem IsShiftInvertC.norm_apply_le {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0) (u : F) :
    ‖X u‖ ≤ |γ.im|⁻¹ * ‖u‖ := by
  have hpos : 0 < |γ.im| := abs_pos.mpr hγ
  have hb : |γ.im| * ‖((⟨X u, h.mem u⟩ : Dom) : F)‖ ≤ ‖cshiftMap A γ ⟨X u, h.mem u⟩‖ :=
    norm_cshiftMap_ge hsym _ _
  rw [show cshiftMap A γ ⟨X u, h.mem u⟩ = u from h.shift_apply u] at hb
  rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
  simpa using hb

theorem IsShiftInvertC.opNorm_le {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0) :
    ‖X‖ ≤ |γ.im|⁻¹ :=
  X.opNorm_le_bound (by positivity) (h.norm_apply_le hsym hγ)

theorem IsShiftInvertC.injective {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) : Function.Injective X := by
  intro u v huv
  have hu := h.shift_apply u
  have hv := h.shift_apply v
  have hsub : (⟨X u, h.mem u⟩ : Dom) = ⟨X v, h.mem v⟩ := Subtype.ext huv
  rw [← hu, ← hv, hsub, huv]

theorem IsShiftInvertC.dom_eq_range {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) : Dom = LinearMap.range (X : F →ₗ[ℂ] F) := by
  apply le_antisymm
  · intro x hx
    exact ⟨cshiftMap A γ ⟨x, hx⟩, h.1 ⟨x, hx⟩⟩
  · rintro _ ⟨u, rfl⟩
    exact h.mem u

theorem IsShiftInvertC.inner_adjoint {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X Y : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hY : IsShiftInvertC A ((starRingEnd ℂ) γ) Y)
    (hsym : SymmetricOn Dom A) (u v : F) :
    (inner ℂ (X u) v : ℂ) = inner ℂ u (Y v) := by
  have hu : γ • X u - A ⟨X u, hX.mem u⟩ = u := hX.shift_apply u
  have hv : (starRingEnd ℂ) γ • Y v - A ⟨Y v, hY.mem v⟩ = v := hY.shift_apply v
  have hcross : (inner ℂ (A ⟨X u, hX.mem u⟩) (Y v) : ℂ)
      = inner ℂ (X u) (A ⟨Y v, hY.mem v⟩) :=
    hsym ⟨X u, hX.mem u⟩ ⟨Y v, hY.mem v⟩
  have e1 : (inner ℂ (X u) v : ℂ)
      = (starRingEnd ℂ) γ * inner ℂ (X u) (Y v) - inner ℂ (X u) (A ⟨Y v, hY.mem v⟩) := by
    conv_lhs => rw [← hv]
    rw [inner_sub_right, inner_smul_right]
  have e2 : (inner ℂ u (Y v) : ℂ)
      = (starRingEnd ℂ) γ * inner ℂ (X u) (Y v) - inner ℂ (A ⟨X u, hX.mem u⟩) (Y v) := by
    conv_lhs => rw [← hu]
    rw [inner_sub_left, inner_smul_left]
  rw [e1, e2, hcross]

theorem shiftInvertC_determines {Dom₁ Dom₂ : Submodule ℂ F} {A₁ : Dom₁ →ₗ[ℂ] F}
    {A₂ : Dom₂ →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h₁ : IsShiftInvertC A₁ γ X) (h₂ : IsShiftInvertC A₂ γ X) :
    Dom₁ = Dom₂ ∧ ∀ (x : F) (hx₁ : x ∈ Dom₁) (hx₂ : x ∈ Dom₂), A₁ ⟨x, hx₁⟩ = A₂ ⟨x, hx₂⟩ := by
  refine ⟨by rw [h₁.dom_eq_range, h₂.dom_eq_range], ?_⟩
  intro x hx₁ hx₂
  set u : F := cshiftMap A₁ γ ⟨x, hx₁⟩ with hu
  have hXu : X u = x := h₁.1 ⟨x, hx₁⟩
  have e₁ : A₁ ⟨X u, h₁.mem u⟩ = γ • X u - u := h₁.apply_eq u
  have e₂ : A₂ ⟨X u, h₂.mem u⟩ = γ • X u - u := h₂.apply_eq u
  have c₁ : (⟨X u, h₁.mem u⟩ : Dom₁) = ⟨x, hx₁⟩ := Subtype.ext hXu
  have c₂ : (⟨X u, h₂.mem u⟩ : Dom₂) = ⟨x, hx₂⟩ := Subtype.ext hXu
  rw [c₁] at e₁
  rw [c₂] at e₂
  rw [e₁, e₂]

theorem isShiftInvertC_unique {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X Y : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hY : IsShiftInvertC A γ Y) : X = Y := by
  ext u
  have h1 : Y (cshiftMap A γ ⟨X u, hX.mem u⟩) = X u := hY.1 ⟨X u, hX.mem u⟩
  rw [show cshiftMap A γ ⟨X u, hX.mem u⟩ = u from hX.shift_apply u] at h1
  exact h1.symm

theorem isShiftInvertC_of_rightInverse {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0)
    (hright : ∀ u : F, ∃ h : X u ∈ Dom, cshiftMap A γ ⟨X u, h⟩ = u) :
    IsShiftInvertC A γ X := by
  refine ⟨fun x => ?_, hright⟩
  obtain ⟨hmem, hval⟩ := hright (cshiftMap A γ x)
  have heq : (⟨X (cshiftMap A γ x), hmem⟩ : Dom) = x :=
    cshiftMap_injective hsym hγ (by rw [hval])
  exact congrArg Subtype.val heq

theorem exists_isShiftInvertC {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A)
    {γ : ℂ} (hγ : γ.im ≠ 0) (hsurj : Function.Surjective (cshiftMap A γ)) :
    ∃ X : F →L[ℂ] F, IsShiftInvertC A γ X := by
  classical
  have hpos : 0 < |γ.im| := abs_pos.mpr hγ
  have hinj : Function.Injective (cshiftMap A γ) := cshiftMap_injective hsym hγ
  choose g hg using hsurj
  have hgshift : ∀ x : Dom, g (cshiftMap A γ x) = x := fun x => hinj (hg _)
  have hadd : ∀ u v : F, ((g (u + v) : Dom) : F) = (g u : F) + (g v : F) := by
    intro u v
    have : cshiftMap A γ (g (u + v)) = cshiftMap A γ (g u + g v) := by
      rw [hg, map_add, hg, hg]
    exact congrArg Subtype.val (hinj this)
  have hsmul : ∀ (c : ℂ) (u : F), ((g (c • u) : Dom) : F) = c • (g u : F) := by
    intro c u
    have : cshiftMap A γ (g (c • u)) = cshiftMap A γ (c • g u) := by
      rw [hg, map_smul, hg]
    exact congrArg Subtype.val (hinj this)
  let L : F →ₗ[ℂ] F :=
    { toFun := fun u => (g u : F)
      map_add' := hadd
      map_smul' := by intro c u; simpa using hsmul c u }
  have hbound : ∀ u : F, ‖L u‖ ≤ |γ.im|⁻¹ * ‖u‖ := by
    intro u
    have hb : |γ.im| * ‖((g u : Dom) : F)‖ ≤ ‖cshiftMap A γ (g u)‖ := norm_cshiftMap_ge hsym _ _
    rw [hg u] at hb
    rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
    exact hb
  refine ⟨L.mkContinuous |γ.im|⁻¹ hbound, fun x => ?_, fun u => ?_⟩
  · change ((g (cshiftMap A γ x) : Dom) : F) = (x : F)
    rw [hgshift x]
  · refine ⟨(g u).2, ?_⟩
    have hsub : (⟨((g u : Dom) : F), (g u).2⟩ : Dom) = g u := Subtype.ext rfl
    change cshiftMap A γ ⟨((g u : Dom) : F), _⟩ = u
    rw [hsub, hg u]

theorem isShiftInvertC_neg_of_isShiftInvert {A : Dom →ₗ[ℂ] F} {c : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A c R) : IsShiftInvertC A (-(c : ℂ)) (-R) := by
  constructor
  · intro x
    have hx : cshiftMap A (-(c : ℂ)) x = -(shiftMap A c x) := by
      simp only [cshiftMap_apply, shiftMap_apply, neg_smul]
      abel
    change (-R) (cshiftMap A (-(c : ℂ)) x) = (x : F)
    rw [hx]
    simp only [ContinuousLinearMap.neg_apply, map_neg, neg_neg]
    exact h.1 x
  · intro u
    have hmemneg : (-R) u ∈ Dom := by
      change -(R u) ∈ Dom
      exact Dom.neg_mem (h.mem u)
    refine ⟨hmemneg, ?_⟩
    have hval : A ⟨R u, h.mem u⟩ + (c : ℂ) • R u = u := h.shift_apply u
    have hcoe : (⟨(-R) u, hmemneg⟩ : Dom) = -(⟨R u, h.mem u⟩ : Dom) := Subtype.ext rfl
    rw [cshiftMap_apply, hcoe, map_neg]
    have hL : (-(c : ℂ)) • (((-(⟨R u, h.mem u⟩ : Dom)) : Dom) : F) - -A ⟨R u, h.mem u⟩
        = A ⟨R u, h.mem u⟩ + (c : ℂ) • R u := by
      simp only [Submodule.coe_neg]
      module
    rw [hL, hval]

theorem shiftInvertC_resolvent_identity {A : Dom →ₗ[ℂ] F} {γ δ : ℂ} {X Y : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hY : IsShiftInvertC A δ Y) (u : F) :
    X u - Y u = (δ - γ) • X (Y u) := by
  have hy : δ • Y u - A ⟨Y u, hY.mem u⟩ = u := hY.shift_apply u
  have hsplit : cshiftMap A γ ⟨Y u, hY.mem u⟩ + (δ - γ) • Y u = u := by
    rw [cshiftMap_apply]
    have hrw : γ • ((⟨Y u, hY.mem u⟩ : Dom) : F) - A ⟨Y u, hY.mem u⟩ + (δ - γ) • Y u
        = δ • Y u - A ⟨Y u, hY.mem u⟩ := by
      module
    rw [hrw, hy]
  have hXu : X u = Y u + (δ - γ) • X (Y u) := by
    conv_lhs => rw [← hsplit]
    rw [map_add, map_smul, hX.1 ⟨Y u, hY.mem u⟩]
  rw [hXu]; abel

theorem shiftInvertC_commute {A : Dom →ₗ[ℂ] F} {γ δ : ℂ} {X Y : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hY : IsShiftInvertC A δ Y) : X ∘L Y = Y ∘L X := by
  rcases eq_or_ne γ δ with rfl | hne
  · rw [isShiftInvertC_unique hX hY]
  · have h1 : ∀ u, X u - Y u = (δ - γ) • X (Y u) :=
      shiftInvertC_resolvent_identity hX hY
    have h2 : ∀ u, Y u - X u = (γ - δ) • Y (X u) :=
      shiftInvertC_resolvent_identity hY hX
    have hd : (δ - γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    ext u
    have h3 : (δ - γ) • X (Y u) = (δ - γ) • Y (X u) := by
      have hneg : (δ - γ) • X (Y u) = -((γ - δ) • Y (X u)) := by
        rw [← h1 u, ← h2 u]; abel
      rw [hneg]; module
    exact smul_right_injective F hd h3

theorem shiftInvertC_comp_one_sub {A : Dom →ₗ[ℂ] F} {γ δ : ℂ} {X Y : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hY : IsShiftInvertC A δ Y) :
    X ∘L (ContinuousLinearMap.id ℂ F - (δ - γ) • Y) = Y := by
  ext u
  have h := shiftInvertC_resolvent_identity hX hY u
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, map_sub, map_smul]
  rw [← h]
  abel

@[simp] theorem rkVec_zero (X : ℕ → F →L[ℂ] F) (v : F) : rkVec X v 0 = v := rfl

@[simp] theorem rkVec_succ (X : ℕ → F →L[ℂ] F) (v : F) (k : ℕ) :
    rkVec X v (k + 1) = X k (rkVec X v k) := rfl

theorem rkSpan_mono (X : ℕ → F →L[ℂ] F) (v : F) {m n : ℕ} (hmn : m ≤ n) :
    rkSpan X v m ≤ rkSpan X v n :=
  Submodule.span_mono (Set.image_mono fun _ hk => lt_of_lt_of_le hk hmn)

@[simp] theorem sirkDen_zero (Xm : F →L[ℂ] F) (c : ℕ → ℂ) :
    sirkDen Xm c 0 = ContinuousLinearMap.id ℂ F := rfl

@[simp] theorem sirkDen_succ (Xm : F →L[ℂ] F) (c : ℕ → ℂ) (k : ℕ) :
    sirkDen Xm c (k + 1) = (ContinuousLinearMap.id ℂ F - c k • Xm) ∘L sirkDen Xm c k := rfl

theorem sirkDen_commute {Xm T : F →L[ℂ] F} (c : ℕ → ℂ) (hT : T ∘L Xm = Xm ∘L T) (k : ℕ) :
    T ∘L sirkDen Xm c k = sirkDen Xm c k ∘L T := by
  induction k with
  | zero => ext u; simp
  | succ k ih =>
      have h1 : T ∘L (ContinuousLinearMap.id ℂ F - c k • Xm)
          = (ContinuousLinearMap.id ℂ F - c k • Xm) ∘L T := by
        ext u
        have := congrArg (fun S : F →L[ℂ] F => S u) hT
        simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at this
        simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
          ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.coe_smul', Pi.smul_apply, map_sub, map_smul, this]
      calc T ∘L ((ContinuousLinearMap.id ℂ F - c k • Xm) ∘L sirkDen Xm c k)
          = (T ∘L (ContinuousLinearMap.id ℂ F - c k • Xm)) ∘L sirkDen Xm c k := rfl
        _ = ((ContinuousLinearMap.id ℂ F - c k • Xm) ∘L T) ∘L sirkDen Xm c k := by rw [h1]
        _ = (ContinuousLinearMap.id ℂ F - c k • Xm) ∘L (T ∘L sirkDen Xm c k) := rfl
        _ = (ContinuousLinearMap.id ℂ F - c k • Xm) ∘L (sirkDen Xm c k ∘L T) := by rw [ih]
        _ = ((ContinuousLinearMap.id ℂ F - c k • Xm) ∘L sirkDen Xm c k) ∘L T := rfl

theorem sirkDen_rkVec {A : Dom →ₗ[ℂ] F} {γ : ℕ → ℂ} {X : ℕ → F →L[ℂ] F} (m : ℕ)
    (hX : ∀ j, IsShiftInvertC A (γ j) (X j)) (v : F) (k : ℕ) :
    sirkDen (X m) (fun i => γ m - γ i) k (rkVec X v k) = (X m ^ k) v := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hcomm : X k ∘L X m = X m ∘L X k :=
        shiftInvertC_commute (hX k) (hX m)
      have hden : X k ∘L sirkDen (X m) (fun i => γ m - γ i) k
          = sirkDen (X m) (fun i => γ m - γ i) k ∘L X k :=
        sirkDen_commute _ hcomm k
      have hkey : (ContinuousLinearMap.id ℂ F - (γ m - γ k) • X m) ∘L X k = X m := by
        have h := shiftInvertC_comp_one_sub (hX k) (hX m)
        have hcomm' : X k ∘L (ContinuousLinearMap.id ℂ F - (γ m - γ k) • X m)
            = (ContinuousLinearMap.id ℂ F - (γ m - γ k) • X m) ∘L X k := by
          ext u
          have := congrArg (fun S : F →L[ℂ] F => S u) hcomm
          simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at this
          simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
            ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
            ContinuousLinearMap.coe_smul', Pi.smul_apply, map_sub, map_smul, this]
        rw [← hcomm', h]
      calc sirkDen (X m) (fun i => γ m - γ i) (k + 1) (rkVec X v (k + 1))
          = (ContinuousLinearMap.id ℂ F - (γ m - γ k) • X m)
              (sirkDen (X m) (fun i => γ m - γ i) k (X k (rkVec X v k))) := rfl
        _ = (ContinuousLinearMap.id ℂ F - (γ m - γ k) • X m)
              (X k (sirkDen (X m) (fun i => γ m - γ i) k (rkVec X v k))) := by
              have := congrArg (fun S : F →L[ℂ] F => S (rkVec X v k)) hden
              simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at this
              rw [← this]
        _ = (ContinuousLinearMap.id ℂ F - (γ m - γ k) • X m) (X k ((X m ^ k) v)) := by rw [ih]
        _ = ((ContinuousLinearMap.id ℂ F - (γ m - γ k) • X m) ∘L X k) ((X m ^ k) v) := rfl
        _ = (X m ^ (k + 1)) v := by
              rw [hkey, pow_succ']
              rfl

section
variable [CompleteSpace F]
theorem rkProj_tendsto (X : ℕ → F →L[ℂ] F) (v : F)
    (hdense : Dense ((⨆ m : ℕ, rkSpan X v m : Submodule ℂ F) : Set F)) (u : F) :
    Tendsto (fun m : ℕ => (rkSpan X v m).starProjection u) atTop (nhds u) :=
  starProjection_tendsto_of_monotone_dense _ (fun _ _ h => rkSpan_mono X v h) hdense u
end

section
variable [CompleteSpace F]
theorem rkCompression_tendsto (T : F →L[ℂ] F) (X : ℕ → F →L[ℂ] F) (v : F)
    (hdense : Dense ((⨆ m : ℕ, rkSpan X v m : Submodule ℂ F) : Set F)) (u : F) :
    Tendsto (fun m : ℕ => rkCompression T X v m u) atTop (nhds (T u)) :=
  compression_tendsto_of_starProjection_tendsto _ T (rkProj_tendsto X v hdense) u
end

section
variable [CompleteSpace F]
theorem hashimoto_multishift_selects_friedrichs (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) {Dom : Submodule ℂ F} (A : Dom →ₗ[ℂ] F)
    (hA : IsPositiveSelfAdjointExtension H A) (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) :
    ∃ X : ℕ → F →L[ℂ] F,
      (∀ j, IsShiftInvertC A (γ j) (X j)) ∧
      (∀ j, ‖X j‖ ≤ |(γ j).im|⁻¹) ∧
      (∀ j, Dom = LinearMap.range ((X j : F →ₗ[ℂ] F))) ∧
      (∀ j k u, X j u - X k u = (γ k - γ j) • X j (X k u)) ∧
      (∀ j k, X j ∘L X k = X k ∘L X j) ∧
      (∀ j m, X j ∘L (ContinuousLinearMap.id ℂ F - (γ m - γ j) • X m) = X m) ∧
      (∀ m v k, sirkDen (X m) (fun i => γ m - γ i) k (rkVec X v k) = (X m ^ k) v) ∧
      (∀ j u, Tendsto (fun n : ℕ => galerkinCompression (X j) b n u) atTop (nhds (X j u))) ∧
      (∀ j (Dom' : Submodule ℂ F) (A' : Dom' →ₗ[ℂ] F), IsShiftInvertC A' (γ j) (X j) →
        Dom' = Dom ∧ ∀ (x : F) (hx : x ∈ Dom) (hx' : x ∈ Dom'), A' ⟨x, hx'⟩ = A ⟨x, hx⟩) := by
  obtain ⟨-, hsym, -, hsa⟩ := hA
  choose X hX using fun j : ℕ =>
    exists_isShiftInvertC hsym (hγ j) (cshiftMap_surjective hsym hsa (hγ j))
  refine ⟨X, hX, fun j => (hX j).opNorm_le hsym (hγ j), fun j => (hX j).dom_eq_range,
    fun j k u => shiftInvertC_resolvent_identity (hX j) (hX k) u,
    fun j k => shiftInvertC_commute (hX j) (hX k),
    fun j m => shiftInvertC_comp_one_sub (hX j) (hX m),
    fun m v k => sirkDen_rkVec m hX v k,
    fun j u => galerkinCompression_tendsto (X j) b u, ?_⟩
  intro j Dom' A' hA'
  obtain ⟨hdom, hval⟩ := shiftInvertC_determines hA' (hX j)
  exact ⟨hdom, fun x hx hx' => hval x hx' hx⟩
end

@[simp] theorem diagLinC_apply {c : ℕ → ℂ} {M : ℝ} (hc : ∀ n, ‖c n‖ ≤ M) (x : ℓ²(ℕ, ℂ)) (n : ℕ) :
    ((diagLinC hc x : ℓ²(ℕ, ℂ)) : ℕ → ℂ) n = c n * x n := rfl

@[simp] theorem diagCLMC_apply {c : ℕ → ℂ} {M : ℝ} (hc : ∀ n, ‖c n‖ ≤ M) (x : ℓ²(ℕ, ℂ)) (n : ℕ) :
    ((diagCLMC hc x : ℓ²(ℕ, ℂ)) : ℕ → ℂ) n = c n * x n := rfl

theorem sub_natCast_ne_zero {γ : ℂ} (hγ : γ.im ≠ 0) (n : ℕ) : γ - (n : ℂ) ≠ 0 := by
  intro h
  have := norm_sub_natCast_ge γ n
  rw [h, norm_zero] at this
  exact hγ (abs_eq_zero.mp (le_antisymm this (abs_nonneg _)))

theorem ell2Example_symmetricOn :
    SymmetricOn (LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ)))
      ell2UnboundedExample :=
  ell2Example_isPositiveSelfAdjointExtension.2.1

theorem ell2ShiftInvert_resolventPre {γ : ℂ} (hγ : γ.im ≠ 0) (u : ℓ²(ℕ, ℂ)) :
    ell2ShiftInvert (ell2ResolventPre hγ u) = ell2Resolvent hγ u := by
  apply lp.ext
  funext n
  have hne : γ - (n : ℂ) ≠ 0 := sub_natCast_ne_zero hγ n
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by
    rw [show ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℂ)) by push_cast; ring]
    exact_mod_cast Nat.succ_ne_zero n
  have hcoe : ((invCoeff n : ℝ) : ℂ) = ((n : ℂ) + 1)⁻¹ := by
    rw [invCoeff]
    push_cast
    rw [one_div]
  rw [ell2ShiftInvert, diagCLM_apply, ell2ResolventPre, diagCLMC_apply, ell2Resolvent,
    diagCLMC_apply, hcoe, preCoeff, resCoeff]
  field_simp

theorem ell2Resolvent_isShiftInvertC {γ : ℂ} (hγ : γ.im ≠ 0) :
    IsShiftInvertC ell2UnboundedExample γ (ell2Resolvent hγ) := by
  refine isShiftInvertC_of_rightInverse ell2Example_symmetricOn hγ ?_
  intro u
  have hR : ell2ShiftInvert (ell2ResolventPre hγ u) = ell2Resolvent hγ u :=
    ell2ShiftInvert_resolventPre hγ u
  have hmem : ell2Resolvent hγ u
      ∈ LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ)) :=
    ⟨ell2ResolventPre hγ u, hR⟩
  refine ⟨hmem, ?_⟩
  have hpre : preim ell2ShiftInvert ⟨ell2Resolvent hγ u, hmem⟩ = ell2ResolventPre hγ u :=
    preim_eq _ ell2ShiftInvert_injective _ hR
  have hA : ell2UnboundedExample ⟨ell2Resolvent hγ u, hmem⟩
      = ell2ResolventPre hγ u - (1 : ℂ) • (ell2Resolvent hγ u) := by
    rw [ell2UnboundedExample, invShiftOperator_apply, hpre]
    norm_num
  rw [cshiftMap_apply]
  change γ • (ell2Resolvent hγ u) - ell2UnboundedExample ⟨ell2Resolvent hγ u, hmem⟩ = u
  rw [hA]
  apply lp.ext
  funext n
  have hne : γ - (n : ℂ) ≠ 0 := sub_natCast_ne_zero hγ n
  simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    ell2Resolvent, ell2ResolventPre, diagCLMC_apply, resCoeff, preCoeff]
  field_simp
  ring

theorem hashimoto_multishift_unbounded_example (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) :
    ∃ X : ℕ → ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ),
      (∀ j u n, ((X j u : ℓ²(ℕ, ℂ)) : ℕ → ℂ) n = (u : ℕ → ℂ) n / (γ j - (n : ℂ))) ∧
      (∀ j, IsShiftInvertC ell2UnboundedExample (γ j) (X j)) ∧
      (∀ j, ‖X j‖ ≤ |(γ j).im|⁻¹) ∧
      (∀ j k u, X j u - X k u = (γ k - γ j) • X j (X k u)) ∧
      (∀ j k, X j ∘L X k = X k ∘L X j) ∧
      (∀ j m, X j ∘L (ContinuousLinearMap.id ℂ (ℓ²(ℕ, ℂ)) - (γ m - γ j) • X m) = X m) ∧
      (∀ m v k, sirkDen (X m) (fun i => γ m - γ i) k (rkVec X v k) = (X m ^ k) v) ∧
      (∀ j u, Tendsto (fun n : ℕ => galerkinCompression (X j) ell2Basis n u) atTop
        (nhds (X j u))) ∧
      (∀ j (Dom' : Submodule ℂ (ℓ²(ℕ, ℂ))) (A' : Dom' →ₗ[ℂ] ℓ²(ℕ, ℂ)),
        IsShiftInvertC A' (γ j) (X j) →
        Dom' = LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ))) ∧
      (∀ C : ℝ, ∃ x : finiteModeDomain ell2Basis,
        C * ‖(x : ℓ²(ℕ, ℂ))‖ < ‖ell2ExampleMatrix x‖) := by
  refine ⟨fun j => ell2Resolvent (hγ j), ?_, fun j => ell2Resolvent_isShiftInvertC (hγ j), ?_, ?_,
    ?_, ?_, ?_, fun j u => galerkinCompression_tendsto _ ell2Basis u, ?_,
    ell2ExampleMatrix_unbounded⟩
  · intro j u n
    have h1 : ((ell2Resolvent (hγ j) u : ℓ²(ℕ, ℂ)) : ℕ → ℂ) n
        = resCoeff (γ j) n * (u : ℕ → ℂ) n := diagCLMC_apply (resCoeff_norm_le (hγ j)) u n
    rw [h1, resCoeff, one_div, inv_mul_eq_div]
  · intro j
    exact (ell2Resolvent_isShiftInvertC (hγ j)).opNorm_le ell2Example_symmetricOn (hγ j)
  · intro j k u
    exact shiftInvertC_resolvent_identity (ell2Resolvent_isShiftInvertC (hγ j))
      (ell2Resolvent_isShiftInvertC (hγ k)) u
  · intro j k
    exact shiftInvertC_commute (ell2Resolvent_isShiftInvertC (hγ j))
      (ell2Resolvent_isShiftInvertC (hγ k))
  · intro j m
    exact shiftInvertC_comp_one_sub (ell2Resolvent_isShiftInvertC (hγ j))
      (ell2Resolvent_isShiftInvertC (hγ m))
  · intro m v k
    exact sirkDen_rkVec m (fun j => ell2Resolvent_isShiftInvertC (hγ j)) v k
  · intro j Dom' A' hA'
    obtain ⟨hdom, -⟩ := shiftInvertC_determines hA' (ell2Resolvent_isShiftInvertC (hγ j))
    exact hdom
end BookProof.HashimotoShiftInvert

open BookProof.HashimotoShiftInvert
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology
open scoped InnerProductSpace ENNReal lp
theorem solution (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) :
    ∃ X : ℕ → ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ),
      (∀ j u n, ((X j u : ℓ²(ℕ, ℂ)) : ℕ → ℂ) n = (u : ℕ → ℂ) n / (γ j - (n : ℂ))) ∧
      (∀ j, IsShiftInvertC ell2UnboundedExample (γ j) (X j)) ∧
      (∀ j, ‖X j‖ ≤ |(γ j).im|⁻¹) ∧
      (∀ j k u, X j u - X k u = (γ k - γ j) • X j (X k u)) ∧
      (∀ j k, X j ∘L X k = X k ∘L X j) ∧
      (∀ j m, X j ∘L (ContinuousLinearMap.id ℂ (ℓ²(ℕ, ℂ)) - (γ m - γ j) • X m) = X m) ∧
      (∀ m v k, sirkDen (X m) (fun i => γ m - γ i) k (rkVec X v k) = (X m ^ k) v) ∧
      (∀ j u, Tendsto (fun n : ℕ => galerkinCompression (X j) ell2Basis n u) atTop
        (nhds (X j u))) ∧
      (∀ j (Dom' : Submodule ℂ (ℓ²(ℕ, ℂ))) (A' : Dom' →ₗ[ℂ] ℓ²(ℕ, ℂ)),
        IsShiftInvertC A' (γ j) (X j) →
        Dom' = LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ))) ∧
      (∀ C : ℝ, ∃ x : finiteModeDomain ell2Basis,
        C * ‖(x : ℓ²(ℕ, ℂ))‖ < ‖ell2ExampleMatrix x‖) := by
  exact BookProof.HashimotoShiftInvert.hashimoto_multishift_unbounded_example γ hγ
#print axioms solution
