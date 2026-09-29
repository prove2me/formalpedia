-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.sectorGround_eq_inf_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:11:00.153497+00:00
-- url     : https://prove2.me/submissions/bfce738e-16e3-485e-a4ec-5b18a866c3d4

-- Generated from ChapterSirkCertifiedGap.lean — solution of BookProof.SirkCertifiedGap.sectorGround_eq_inf_eigenvalues
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
import Theorems.Thm_BookProof_SirkCertifiedGap_sectorRestrict_isSymmetric
import Theorems.Thm_BookProof_SirkCertifiedGap_rayleigh_sectorRestrict
import Theorems.Thm_BookProof_SirkCertifiedGap_sectorGround_le_rayleigh
import Theorems.Thm_BookProof_SirkCertifiedGap_le_sectorGround
import Theorems.Thm_BookProof_SirkFinitePrecision_ground_le_rayleigh
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkCertifiedGap











noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {T P : E →ₗ[ℂ] E} {s : ℝ}
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
