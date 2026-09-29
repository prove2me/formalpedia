-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.sectorGround_ge_temple
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:27:43.654036+00:00
-- url     : https://prove2.me/submissions/274c1ea2-0395-4f07-8284-2eb4faaee953

/- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0. https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean
Supporting finite-dimensional Temple proof from ChapterSirkFinitePrecision.lean, same revision. -/
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
set_option maxHeartbeats 4000000
set_option autoImplicit false
noncomputable section
namespace BookProof.SirkFinitePrecision
open scoped InnerProductSpace
open Finset
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
theorem repr_apply_of_symmetric {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (x : E) (i : Fin n) :
    coeff hT hn (T x) i = (hT.eigenvalues hn i : ℂ) * coeff hT hn x i := by
  rw [coeff, coeff, OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply,
    ← hT, hT.apply_eigenvectorBasis hn i, inner_smul_left]
  simp

theorem norm_sq_eq_sum_repr {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (x : E) :
    ‖x‖ ^ 2 = ∑ i, ‖coeff hT hn x i‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).repr.norm_map x]
  exact EuclideanSpace.norm_sq_eq _

theorem rayleigh_eq_sum_eigenvalues {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (x : E) :
    rayleigh T x = ∑ i, hT.eigenvalues hn i * ‖coeff hT hn x i‖ ^ 2 := by
  classical
  have hinner : inner ℂ x (T x)
      = inner ℂ ((hT.eigenvectorBasis hn).repr x) ((hT.eigenvectorBasis hn).repr (T x)) :=
    ((hT.eigenvectorBasis hn).repr.inner_map_map x (T x)).symm
  rw [rayleigh, hinner, PiLp.inner_apply, Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  have hc : ((hT.eigenvectorBasis hn).repr (T x)).ofLp i
      = (hT.eigenvalues hn i : ℂ) * coeff hT hn x i := repr_apply_of_symmetric hT hn x i
  rw [show ((hT.eigenvectorBasis hn).repr x).ofLp i = coeff hT hn x i from rfl, hc,
    RCLike.inner_apply, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_mul, Complex.ofReal_re]

theorem norm_apply_sq_eq_sum_eigenvalues {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (x : E) :
    ‖T x‖ ^ 2 = ∑ i, hT.eigenvalues hn i ^ 2 * ‖coeff hT hn x i‖ ^ 2 := by
  rw [norm_sq_eq_sum_repr hT hn (T x)]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [repr_apply_of_symmetric hT hn x i, norm_mul]
  simp [mul_pow, sq_abs]

theorem index_nonempty {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) {x : E} (hx : x ≠ 0) :
    (univ : Finset (Fin n)).Nonempty := by
  rcases Finset.eq_empty_or_nonempty (univ : Finset (Fin n)) with h | h
  · exfalso
    apply hx
    have hsum := norm_sq_eq_sum_repr hT hn x
    rw [h, Finset.sum_empty] at hsum
    have : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
    exact norm_eq_zero.mp this
  · exact h

theorem ground_le_rayleigh {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) {x : E} (hx : ‖x‖ = 1) {lam0 : ℝ}
    (hlow : ∀ i, lam0 ≤ hT.eigenvalues hn i) :
    lam0 ≤ rayleigh T x := by
  classical
  have hpar : (1 : ℝ) = ∑ i, ‖coeff hT hn x i‖ ^ 2 := by
    rw [← norm_sq_eq_sum_repr hT hn x, hx]; norm_num
  rw [rayleigh_eq_sum_eigenvalues hT hn x]
  calc lam0 = ∑ i, lam0 * ‖coeff hT hn x i‖ ^ 2 := by
        rw [← Finset.mul_sum, ← hpar, mul_one]
    _ ≤ ∑ i, hT.eigenvalues hn i * ‖coeff hT hn x i‖ ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hlow i) (by positivity)

theorem temple_lower_bound {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) {x : E} (hx : ‖x‖ = 1) {lam0 β : ℝ}
    (hsep : ∀ i, hT.eigenvalues hn i = lam0 ∨ β ≤ hT.eigenvalues hn i)
    (hlow : ∀ i, lam0 ≤ hT.eigenvalues hn i)
    (hβ : rayleigh T x < β) :
    rayleigh T x - (‖T x‖ ^ 2 - rayleigh T x ^ 2) / (β - rayleigh T x) ≤ lam0 := by
  classical
  have hpar : (1 : ℝ) = ∑ i, ‖coeff hT hn x i‖ ^ 2 := by
    rw [← norm_sq_eq_sum_repr hT hn x, hx]; norm_num
  have hquad : 0 ≤ ∑ i, (hT.eigenvalues hn i - lam0) * (hT.eigenvalues hn i - β)
      * ‖coeff hT hn x i‖ ^ 2 := by
    refine Finset.sum_nonneg ?_
    intro i _
    have hcoord : (0 : ℝ) ≤ ‖coeff hT hn x i‖ ^ 2 := by positivity
    rcases hsep i with h | h
    · rw [h]; simp
    · have h0 : 0 ≤ hT.eigenvalues hn i - lam0 := by linarith [hlow i]
      have h1 : 0 ≤ hT.eigenvalues hn i - β := by linarith
      exact mul_nonneg (mul_nonneg h0 h1) hcoord
  have hexp : ∑ i, (hT.eigenvalues hn i - lam0) * (hT.eigenvalues hn i - β)
      * ‖coeff hT hn x i‖ ^ 2
      = ‖T x‖ ^ 2 - (lam0 + β) * rayleigh T x + lam0 * β := by
    have hsplit : ∑ i, (hT.eigenvalues hn i - lam0) * (hT.eigenvalues hn i - β)
        * ‖coeff hT hn x i‖ ^ 2
        = (∑ i, hT.eigenvalues hn i ^ 2 * ‖coeff hT hn x i‖ ^ 2)
          - (lam0 + β) * (∑ i, hT.eigenvalues hn i * ‖coeff hT hn x i‖ ^ 2)
          + lam0 * β * (∑ i, ‖coeff hT hn x i‖ ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, ← norm_apply_sq_eq_sum_eigenvalues hT hn x,
      ← rayleigh_eq_sum_eigenvalues hT hn x, ← hpar, mul_one]
  rw [hexp] at hquad
  have hβθ : 0 < β - rayleigh T x := by linarith
  have hdiv : rayleigh T x - lam0
      ≤ (‖T x‖ ^ 2 - rayleigh T x ^ 2) / (β - rayleigh T x) := by
    rw [le_div_iff₀ hβθ]
    nlinarith [hquad]
  linarith
end BookProof.SirkFinitePrecision
namespace BookProof.SirkCertifiedGap
open scoped InnerProductSpace
open Finset Filter Topology BookProof.SirkFinitePrecision
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
@[simp] theorem sectorRestrict_coe {T P : E →ₗ[ℂ] E} {s : ℝ} (hcomm : ∀ x, T (P x) = P (T x)) (y : paritySector P s) : ((sectorRestrict T P s hcomm) y : E) = T (y : E) := rfl

theorem sectorRestrict_isSymmetric {T P : E →ₗ[ℂ] E} {s : ℝ}
    (hcomm : ∀ x, T (P x) = P (T x)) (hT : T.IsSymmetric) :
    (sectorRestrict T P s hcomm).IsSymmetric := by
  intro x y
  simpa [sectorRestrict, Submodule.coe_inner] using hT x.val y.val

theorem rayleigh_sectorRestrict {T P : E →ₗ[ℂ] E} {s : ℝ} (hcomm : ∀ x, T (P x) = P (T x))
    (y : paritySector P s) : rayleigh (sectorRestrict T P s hcomm) y = rayleigh T (y : E) := by
  simp [rayleigh, Submodule.coe_inner]

theorem sectorRayleighSet_bddBelow {T : E →ₗ[ℂ] E} (P : E →ₗ[ℂ] E) (s : ℝ)
    (hT : T.IsSymmetric) : BddBelow (sectorRayleighSet T P s) := by
  classical
  rcases Set.eq_empty_or_nonempty (sectorRayleighSet T P s) with h | ⟨r, x, hx, -, -⟩
  · rw [h]; exact bddBelow_empty
  · have hx0 : x ≠ 0 := by
      intro h; rw [h] at hx; simp at hx
    have hne := index_nonempty hT rfl hx0
    refine ⟨univ.inf' hne fun i => hT.eigenvalues (rfl : Module.finrank ℂ E = _) i, ?_⟩
    rintro r ⟨y, hy, -, rfl⟩
    exact ground_le_rayleigh hT rfl hy fun i => Finset.inf'_le _ (mem_univ i)

theorem sectorGround_le_rayleigh {T : E →ₗ[ℂ] E} {P : E →ₗ[ℂ] E} {s : ℝ}
    (hT : T.IsSymmetric) {x : E} (hx : ‖x‖ = 1) (hmem : x ∈ paritySector P s) :
    sectorGround T P s ≤ rayleigh T x :=
  csInf_le (sectorRayleighSet_bddBelow P s hT) ⟨x, hx, hmem, rfl⟩

theorem le_sectorGround {T P : E →ₗ[ℂ] E} {s c : ℝ}
    (hne : (sectorRayleighSet T P s).Nonempty)
    (hlb : ∀ x : E, ‖x‖ = 1 → x ∈ paritySector P s → c ≤ rayleigh T x) :
    c ≤ sectorGround T P s := by
  refine le_csInf hne ?_
  rintro r ⟨x, hx, hmem, rfl⟩
  exact hlb x hx hmem

theorem sectorGround_eq_inf_eigenvalues {T P : E →ₗ[ℂ] E} {s : ℝ}
    (hcomm : ∀ x, T (P x) = P (T x)) (hT : T.IsSymmetric)
    (hne : (univ : Finset (Fin (Module.finrank ℂ (paritySector P s)))).Nonempty) :
    sectorGround T P s
      = univ.inf' hne fun i =>
          (sectorRestrict_isSymmetric (s := s) hcomm hT).eigenvalues (rfl) i := by
  classical
  set S := sectorRestrict T P s hcomm with hS
  set hSym := sectorRestrict_isSymmetric (s := s) hcomm hT with hSymdef
  set b := hSym.eigenvectorBasis (rfl : Module.finrank ℂ (paritySector P s) = _) with hb
  set m := univ.inf' hne fun i => hSym.eigenvalues (rfl) i with hm
  -- the infimum is attained at an eigenvector
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image univ (fun i => hSym.eigenvalues (rfl) i) hne
  have hmi0 : m = hSym.eigenvalues (rfl) i0 :=
    le_antisymm (Finset.inf'_le _ (mem_univ i0))
      (Finset.le_inf' hne _ fun i _ => hi0 i (mem_univ i))
  have hunit : ‖((b i0 : paritySector P s) : E)‖ = 1 := b.orthonormal.1 i0
  have hmem : ((b i0 : paritySector P s) : E) ∈ paritySector P s := (b i0).2
  have hray : rayleigh T ((b i0 : paritySector P s) : E) = hSym.eigenvalues (rfl) i0 := by
    have hR : rayleigh S (b i0) = rayleigh T ((b i0 : paritySector P s) : E) :=
      rayleigh_sectorRestrict hcomm (b i0)
    have happ : S (b i0) = (hSym.eigenvalues (rfl) i0 : ℂ) • b i0 :=
      hSym.apply_eigenvectorBasis (rfl) i0
    have : rayleigh S (b i0) = hSym.eigenvalues (rfl) i0 := by
      rw [rayleigh, happ, inner_smul_right]
      have hnb : (inner ℂ (b i0) (b i0) : ℂ) = 1 := by
        have := b.orthonormal.1 i0
        rw [inner_self_eq_norm_sq_to_K]
        simp [this]
      rw [hnb]
      simp
    rw [← hR, this]
  refine le_antisymm ?_ ?_
  · rw [hmi0, ← hray]
    exact sectorGround_le_rayleigh hT hunit hmem
  · refine le_sectorGround ⟨_, _, hunit, hmem, rfl⟩ ?_
    intro x hx hmemx
    have hxS : (⟨x, hmemx⟩ : paritySector P s) ≠ 0 := by
      intro h
      have : x = 0 := congrArg Subtype.val h
      rw [this] at hx; simp at hx
    have hnorm : ‖(⟨x, hmemx⟩ : paritySector P s)‖ = 1 := by simpa using hx
    have := ground_le_rayleigh hSym (rfl) hnorm
      (lam0 := m) (fun i => by rw [hm]; exact Finset.inf'_le _ (mem_univ i))
    rwa [rayleigh_sectorRestrict hcomm ⟨x, hmemx⟩] at this

theorem sectorGround_ge_temple {T P : E →ₗ[ℂ] E} {s : ℝ}
    (hcomm : ∀ x, T (P x) = P (T x)) (hT : T.IsSymmetric)
    {y : paritySector P s} (hy : ‖y‖ = 1)
    (hne : (univ : Finset (Fin (Module.finrank ℂ (paritySector P s)))).Nonempty)
    {β : ℝ}
    (hsep : ∀ i, (sectorRestrict_isSymmetric (s := s) hcomm hT).eigenvalues (rfl) i
        = sectorGround T P s
      ∨ β ≤ (sectorRestrict_isSymmetric (s := s) hcomm hT).eigenvalues (rfl) i)
    (hβ : rayleigh T (y : E) < β) :
    rayleigh T (y : E)
        - (‖T (y : E)‖ ^ 2 - rayleigh T (y : E) ^ 2) / (β - rayleigh T (y : E))
      ≤ sectorGround T P s := by
  classical
  set hSym := sectorRestrict_isSymmetric (s := s) hcomm hT with hSymdef
  have hground := sectorGround_eq_inf_eigenvalues hcomm hT hne
  have hlow : ∀ i, sectorGround T P s ≤ hSym.eigenvalues (rfl) i := by
    intro i
    rw [hground]
    exact Finset.inf'_le _ (mem_univ i)
  have hray : rayleigh (sectorRestrict T P s hcomm) y = rayleigh T (y : E) :=
    rayleigh_sectorRestrict hcomm y
  have hnorm : ‖(sectorRestrict T P s hcomm) y‖ = ‖T (y : E)‖ := by
    simp
  have := temple_lower_bound hSym (rfl) hy (lam0 := sectorGround T P s) (β := β)
    hsep hlow (by rwa [hray])
  rwa [hray, hnorm] at this
end BookProof.SirkCertifiedGap

open scoped InnerProductSpace
open Finset Filter Topology BookProof.SirkFinitePrecision BookProof.SirkCertifiedGap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
theorem solution {T P : E →ₗ[ℂ] E} {s : ℝ}
    (hcomm : ∀ x, T (P x) = P (T x)) (hT : T.IsSymmetric)
    {y : paritySector P s} (hy : ‖y‖ = 1)
    (hne : (univ : Finset (Fin (Module.finrank ℂ (paritySector P s)))).Nonempty)
    {β : ℝ}
    (hsep : ∀ i, (sectorRestrict_isSymmetric (s := s) hcomm hT).eigenvalues (rfl) i
        = sectorGround T P s
      ∨ β ≤ (sectorRestrict_isSymmetric (s := s) hcomm hT).eigenvalues (rfl) i)
    (hβ : rayleigh T (y : E) < β) :
    rayleigh T (y : E)
        - (‖T (y : E)‖ ^ 2 - rayleigh T (y : E) ^ 2) / (β - rayleigh T (y : E))
      ≤ sectorGround T P s := by
  exact BookProof.SirkCertifiedGap.sectorGround_ge_temple hcomm hT hy hne hsep hβ
#print axioms solution
