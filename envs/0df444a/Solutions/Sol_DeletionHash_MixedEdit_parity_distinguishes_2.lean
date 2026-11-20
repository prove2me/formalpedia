-- Prove2me | solution 2 for DeletionHash.MixedEdit.parity_distinguishes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:09:44.440726+00:00
-- url     : https://prove2.me/submissions/9fa65bef-7822-4bec-b478-905e1d61ce07

import Definitions.Def_DeletionHash_MixedEdit_Paths
import Definitions.Def_DeletionHash_MixedEdit_Regime
import Definitions.Def_DeletionHash_MixedEdit_UniqueWords
import Mathlib
import Theorems.Thm_DeletionHash_MixedEdit_spectrum_simple_path

/- Adapted from Eyal En Gad, deletion-codes-lean, commit 24d093a4 (Apache-2.0). Alphabet generalization preserves the original reconstruction proof. -/
namespace DeletionGraph.OverlapCollision
variable (α : Type*) [Fintype α]
abbrev Bits (n : ℕ) := Fin n → α
def padBits {n : ℕ} (x : Bits α n) (i : ℕ) : Option α :=
  if hi : i < n then some (x ⟨i, hi⟩) else none
def Agree (p : ℕ → Option α) (a : ℕ) (q : ℕ → Option α) (b k : ℕ) : Prop :=
  ∀ i, i < k → p (a+i) = q (b+i)

end DeletionGraph.OverlapCollision
namespace DeletionGraph.UniqueWordCount
open OverlapCollision
variable (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α]
attribute [local instance] Classical.propDecidable

def KUnique (p : ℕ → Option α) (n k : ℕ) : Prop :=
  ∀ a b, a+k ≤ n → b+k ≤ n → Agree α p a p b k → a=b
noncomputable def uniqueWords (n k : ℕ) : Finset (Bits α n) := by
  classical
  exact Finset.univ.filter (fun x => KUnique α (padBits α x) n k)


end DeletionGraph.UniqueWordCount
namespace DeletionGraph.UniqueBridge
open DeletionHash.MixedEdit
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem window_as_ofFn {n k a : ℕ} (x : Word α n) (ha : a+k ≤ n) :
    window k (letters x) a = List.ofFn (fun i : Fin k => x ⟨a+i.val, by omega⟩) := by
  apply List.ext_getElem
  · simp only [window, letters, List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro i hi hj
    simp only [window, letters, List.getElem_take, List.getElem_drop, List.getElem_ofFn]

theorem window_eq_iff {n k a b : ℕ} (x : Word α n)
    (ha : a+k ≤ n) (hb : b+k ≤ n) :
    window k (letters x) a = window k (letters x) b ↔
      OverlapCollision.Agree α (OverlapCollision.padBits α x) a
        (OverlapCollision.padBits α x) b k := by
  rw [window_as_ofFn x ha, window_as_ofFn x hb, List.ofFn_inj]
  constructor
  · intro h i hi
    have he := congrFun h (⟨i, hi⟩ : Fin k)
    simpa only [OverlapCollision.padBits, dif_pos (show a+i<n by omega),
      dif_pos (show b+i<n by omega), Option.some.injEq] using he
  · intro h
    funext i
    have he := h i.val i.isLt
    simpa only [OverlapCollision.padBits, dif_pos (show a+i.val<n by omega),
      dif_pos (show b+i.val<n by omega), Option.some.injEq] using he

theorem unique_iff {n k : ℕ} (x : Word α n) :
    IsUnique k (letters x) ↔ UniqueWordCount.KUnique α (OverlapCollision.padBits α x) n k := by
  unfold IsUnique windows starts
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  simp only [List.mem_range, letters, List.length_ofFn]
  constructor
  · intro h a b ha hb hab
    have hkn : k ≤ n := by omega
    apply h a (by simp only [if_pos hkn]; omega) b (by simp only [if_pos hkn]; omega)
    exact (window_eq_iff x ha hb).mpr hab
  · intro h a ha b hb hab
    by_cases hkn : k ≤ n
    · simp only [if_pos hkn] at ha hb
      exact h a b (by omega) (by omega) ((window_eq_iff x (by omega) (by omega)).mp hab)
    · simp only [if_neg hkn] at ha
      omega

theorem family_eq (n k : ℕ) : uniqueFamily α n k = UniqueWordCount.uniqueWords α n k := by
  classical
  ext x
  simp only [uniqueFamily, UniqueWordCount.uniqueWords, Finset.mem_filter,
    Finset.mem_univ, true_and, unique_iff]

end DeletionGraph.UniqueBridge
namespace DeletionGraph.SpectrumPath
open DeletionHash.MixedEdit UniqueBridge
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem nonzero_iff_mem (L : ℕ) (x : List α) (g : Gram α L) :
    spectrum L x g ≠ 0 ↔ List.ofFn g ∈ windows L x := by
  simp [DeletionHash.MixedEdit.spectrum, List.count_eq_zero]

theorem windows_mem_iff {n L : ℕ} (x : Word α n) (g : Gram α L) :
    List.ofFn g ∈ windows L (letters x) ↔
      ∃ a, a+L ≤ n ∧ window L (letters x) a = List.ofFn g := by
  unfold windows starts
  simp only [List.mem_map, List.mem_range, letters, List.length_ofFn]
  constructor
  · rintro ⟨a, ha, hg⟩
    by_cases h : L ≤ n
    · simp only [if_pos h] at ha
      exact ⟨a, by omega, hg⟩
    · simp only [if_neg h] at ha
      omega
  · rintro ⟨a, ha, hg⟩
    refine ⟨a, ?_, hg⟩
    rw [if_pos (show L ≤ n by omega)]
    omega


end DeletionGraph.SpectrumPath

namespace DeletionGraph.Parity
open DeletionHash.MixedEdit SpectrumPath UniqueBridge
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem distinguishes {n L : ℕ} (x z : Word α n) (hL : 1 ≤ L) (hn : L ≤ n)
    (hq : 2 ≤ Fintype.card α) (hk : uniqueLength (Fintype.card α) n < L)
    (hx : IsUnique (L-1) (letters x)) (hne : z ≠ x) :
    parity (spectrum L (letters z) - spectrum L (letters x)) ≠ 0 := by
  intro hp
  have hlarge : IsUnique L (letters x) := (unique_iff x).mpr (by
    have hsmall := (unique_iff x).mp hx
    intro a b ha hb hab
    apply hsmall a b (by omega) (by omega)
    intro i hi
    exact hab i (by omega))
  have hsupp : ∀ g : Gram α L, List.ofFn g ∈ windows L (letters x) →
      List.ofFn g ∈ windows L (letters z) := by
    intro g hg
    have hx0 := (nonzero_iff_mem L (letters x) g).mpr hg
    have hx1 : spectrum L (letters x) g = 1 := ((DeletionHash.MixedEdit.spectrum_simple_path n L hq hk hn x hx).1 g).resolve_left hx0
    apply (nonzero_iff_mem L (letters z) g).mp
    intro hz0
    have h := congrFun hp g
    change ((spectrum L (letters z) g - spectrum L (letters x) g : ℤ) : ZMod 2) = 0 at h
    rw [hz0, hx1] at h
    norm_num at h
  have hsub : windows L (letters x) ⊆ windows L (letters z) := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    have hab : a+L ≤ n := by
      simp only [starts, letters, List.length_ofFn, List.mem_range, if_pos hn] at ha
      omega
    rw [window_as_ofFn x hab]
    apply hsupp
    exact (windows_mem_iff x _).mpr ⟨a, hab, window_as_ofFn x hab⟩
  have hperm := (List.Nodup.subperm hlarge hsub).perm_of_length_le (by
    simp only [windows, starts, letters, List.length_map, List.length_range, List.length_ofFn, le_refl])
  apply hne
  apply (DeletionHash.MixedEdit.spectrum_simple_path n L hq hk hn x hx).2.2 z
  funext g
  unfold DeletionHash.MixedEdit.spectrum
  exact_mod_cast (hperm.count_eq (List.ofFn g)).symm

end DeletionGraph.Parity
open DeletionHash.MixedEdit

universe u

/-- Lemma 3.3: the partner is an arbitrary word of the same length. -/
theorem solution {α : Type u} [Fintype α] [DecidableEq α]
    (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique (L-1) (letters x)) :
    ∀ z : Word α n, z ≠ x → parity (spectrum L (letters z) - spectrum L (letters x)) ≠ 0 := by
  obtain ⟨hq, ht, hb, hk, hL, hbk, hn⟩ := hreg
  letI : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  intro z hne
  exact DeletionGraph.Parity.distinguishes x z (by omega) hn hq (by omega) hx hne



#print axioms solution
