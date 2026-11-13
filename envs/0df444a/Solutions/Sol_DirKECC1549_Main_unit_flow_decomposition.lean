-- Prove2me | solution 1 for DirKECC1549.Main.unit_flow_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T10:31:01.617097+00:00
-- url     : https://prove2.me/submissions/0e8338e0-ec73-48ab-89ec-d472878ec05d

import Theorems.Thm_DirKECC1549_Main_trail_family_flow
import Theorems.Thm_DirKECC1549_Main_unit_flow_extract_trail
set_option autoImplicit false
open DirKECC1549.Main

private theorem paths_of_flow {n m : ℕ} (D : Fin m → Fin n × Fin n) (u v : Fin n)
    (huv : u ≠ v) (q : ℕ) (F : Finset (Fin m)) (hF : IsUnitFlow D F u v q) :
    ∃ P : Fin q → List (Fin m), (∀ i, IsTrail D u (P i) v) ∧
      (∀ i j, i ≠ j → Disjoint (P i).toFinset (P j).toFinset) ∧
      ∀ i, (P i).toFinset ⊆ F := by
  classical
  induction q generalizing F with
  | zero =>
    refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_, ?_⟩ <;> intro i <;> exact Fin.elim0 i
  | succ q ih =>
    obtain ⟨p, hp, hpF, hrem⟩ := unit_flow_extract_trail D u v huv q F hF
    obtain ⟨P, hP, hd, hsub⟩ := ih (F \ p.toFinset) hrem
    refine ⟨Fin.cases p P, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa using hp
      · simpa using hP j
    · intro i
      refine Fin.cases ?_ (fun i' ↦ ?_) i
      · intro j
        refine Fin.cases ?_ (fun j' ↦ ?_) j
        · intro hij
          exact False.elim (hij rfl)
        · intro hij
          apply Finset.disjoint_left.mpr
          intro e he he'
          have hrem' := hsub j' (by simpa using he')
          simp only [Finset.mem_sdiff] at hrem'
          exact hrem'.2 (by simpa using he)
      · intro j
        refine Fin.cases ?_ (fun j' ↦ ?_) j
        · intro hij
          apply Finset.disjoint_left.mpr
          intro e he he'
          have hrem' := hsub i' (by simpa using he)
          simp only [Finset.mem_sdiff] at hrem'
          exact hrem'.2 (by simpa using he')
        · intro hij
          apply hd
          intro he
          apply hij
          simpa [he]
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa using hpF
      · intro e he
        have hh := hsub j (by simpa using he)
        exact (Finset.mem_sdiff.mp hh).1

theorem solution {n m : ℕ} (D : Fin m → Fin n × Fin n)
    (u v : Fin n) (huv : u ≠ v) (q : ℕ) :
    HasDisjointPaths D q u v ↔ ∃ F : Finset (Fin m), IsUnitFlow D F u v q := by
  classical
  constructor
  · rintro ⟨P, hP, hd⟩
    exact ⟨Finset.univ.biUnion (fun i ↦ (P i).toFinset), trail_family_flow D u v q P hP hd⟩
  · rintro ⟨F, hF⟩
    obtain ⟨P, hP, hd, _⟩ := paths_of_flow D u v huv q F hF
    exact ⟨P, hP, hd⟩
