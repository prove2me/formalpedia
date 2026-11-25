-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.neighbourBasic_unimod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:52:53.65937+00:00
-- url     : https://prove2.me/submissions/d2c226dd-510b-4b44-a8cf-c425d7330128

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourBasic_smul_mem
import Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourBasic_gen
import Theorems.Thm_P2M_Formalism_HermitianLatticesTheory_neighbourBasic_gen__90f7c5007d13
import Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourBasic_not_le
import Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourBasic_ded
import Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourBasic_h_smul_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourBasic_h_smul_right
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution [IsDedekindDomain R] [IsFractionRing R K]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (P : Ideal R) (hP : P.IsMaximal) (hPc : (conjIdeal (K := K) P).IsMaximal)
    (L M : Submodule R V)
    (eL : (L ⧸ (L ⊓ M).comap L.subtype) ≃ₗ[R] (R ⧸ conjIdeal (K := K) P))
    (eM : (M ⧸ (L ⊓ M).comap M.subtype) ≃ₗ[R] (R ⧸ P))
    (hL : IsUnimodular h L) (hM : IsIntegralLat h M) : IsUnimodular h M := by
  have hone : ∀ k : K, k ∈ (1 : Submodule R K) ↔ k ∈ Set.range (algebraMap R K) :=
    fun k => by rw [Submodule.mem_one]; rfl
  have rmul : ∀ a b : K, a ∈ Set.range (algebraMap R K) → b ∈ Set.range (algebraMap R K) →
      a * b ∈ Set.range (algebraMap R K) := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x * y, map_mul _ _ _⟩
  have radd : ∀ a b : K, a ∈ Set.range (algebraMap R K) → b ∈ Set.range (algebraMap R K) →
      a + b ∈ Set.range (algebraMap R K) := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, map_add _ _ _⟩
  have ralg : ∀ r : R, algebraMap R K r ∈ Set.range (algebraMap R K) := fun r => ⟨r, rfl⟩
  have rstar : ∀ a : K, a ∈ Set.range (algebraMap R K) → star a ∈ Set.range (algebraMap R K) := by
    rintro _ ⟨x, rfl⟩; exact hstar x
  have memD : ∀ (A : Submodule R V) (x : V),
      x ∈ dual h A ↔ ∀ y ∈ A, h y x ∈ Set.range (algebraMap R K) := by
    intro A x; rw [dualBasic_mem_dual]; simp only [hone]
  have hMM : ∀ m ∈ M, m ∈ dual h M := fun m hm =>
    (memD M m).mpr (fun y hy => (hone _).mp (hM y hy m hm))
  obtain ⟨l₀, hl₀, hgen⟩ := neighbourBasic_gen eL
  obtain ⟨m₀, hm₀, hm₀N⟩ := neighbourBasic_not_le hP.ne_top eM
  have hm₀L : m₀ ∉ L := fun h' => hm₀N (Submodule.mem_inf.mpr ⟨h', hm₀⟩)
  have gen : ∀ y : V, (∀ n ∈ L ⊓ M, h n y ∈ Set.range (algebraMap R K)) →
      h l₀ y ∈ Set.range (algebraMap R K) → y ∈ L := by
    intro y hN h0
    rw [← hL, memD]
    intro l hl
    obtain ⟨a, ha⟩ := hgen l hl
    have e1 : l = a • l₀ + (l - a • l₀) := by abel
    rw [e1, map_add, LinearMap.add_apply, neighbourBasic_h_smul_left]
    exact radd _ _ (rmul _ _ (rstar _ (ralg a)) h0) (hN _ ha)
  have hNM : ∀ y ∈ dual h M, ∀ n ∈ L ⊓ M, h n y ∈ Set.range (algebraMap R K) :=
    fun y hy n hn => (memD M y).mp hy n (Submodule.mem_inf.mp hn).2
  have hPy : ∀ y ∈ dual h M, ∀ p ∈ P,
      algebraMap R K p * h l₀ y ∈ Set.range (algebraMap R K) := by
    intro y hy p hp
    obtain ⟨t, ht⟩ := hstar p
    have htP : t ∈ conjIdeal (K := K) P := Ideal.subset_span ⟨p, hp, ht⟩
    have := hNM y hy _ (neighbourBasic_smul_mem eL htP hl₀)
    rwa [neighbourBasic_h_smul_left, ht, star_star] at this
  have stepA : ∀ y ∈ L, y ∈ dual h M → y ∈ M := by
    intro y hyL hyM
    by_contra hyN'
    have hyN : y ∉ L ⊓ M := fun h' => hyN' (Submodule.mem_inf.mp h').2
    apply hm₀L
    rw [← hL, memD]
    intro l hl
    have hlD : l ∈ dual h M := by
      obtain ⟨a, ha⟩ := neighbourBasic_gen' hPc eL hyL hyN l hl
      have e1 : l = (l - a • y) + a • y := by abel
      rw [e1]
      exact (dual h M).add_mem (hMM _ (Submodule.mem_inf.mp ha).2) ((dual h M).smul_mem a hyM)
    have := (memD M l).mp hlD m₀ hm₀
    rw [← hs.eq m₀ l, starRingEnd_apply]
    exact rstar _ this
  show dual h M = M
  refine le_antisymm ?_ (fun m hm => hMM m hm)
  intro x hx
  have hm₀D := hMM m₀ hm₀
  have hc' : h l₀ m₀ ∉ Set.range (algebraMap R K) := fun h' => hm₀L (gen m₀ (hNM m₀ hm₀D) h')
  obtain ⟨a, b, hab⟩ :=
    neighbourBasic_ded P hP (h l₀ x) (h l₀ m₀) (hPy x hx) (hPy m₀ hm₀D) hc'
  have hyD : x - b • m₀ ∈ dual h M := (dual h M).sub_mem hx ((dual h M).smul_mem b hm₀D)
  have hy0 : h l₀ (x - b • m₀) ∈ Set.range (algebraMap R K) := by
    rw [map_sub, neighbourBasic_h_smul_right, hab]; exact ⟨a, by ring⟩
  have hyM := stepA _ (gen _ (hNM _ hyD) hy0) hyD
  have e1 : x = (x - b • m₀) + b • m₀ := by abel
  rw [e1]
  exact M.add_mem hyM (M.smul_mem b hm₀)
end Formalism.HermitianLatticesTheory
