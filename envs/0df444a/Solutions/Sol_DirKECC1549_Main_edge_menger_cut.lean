-- Prove2me | solution 1 for DirKECC1549.Main.edge_menger_cut
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T10:18:18.393794+00:00
-- url     : https://prove2.me/submissions/1beafb5f-7a9a-4770-9377-140b70bccd56

import Theorems.Thm_DirKECC1549_Main_sec2_maxflow_mincut
set_option autoImplicit false
open DirKECC1549.Main

private theorem path_count_bound {n m : ℕ} (D : Fin m → Fin n × Fin n) (x y : Fin n)
    (hxy : x ≠ y) (k : ℕ) (h : HasDisjointPaths D k x y) : k ≤ m := by
  classical
  obtain ⟨P, hP, hd⟩ := h
  have hne : ∀ i, P i ≠ [] := by
    intro i hi
    have hw := (hP i).1
    rw [hi] at hw
    cases hw
    exact hxy rfl
  have hex : ∀ i, ∃ e, e ∈ P i := by
    intro i
    cases hp : P i with
    | nil => exact False.elim (hne i hp)
    | cons e p => exact ⟨e, by simp⟩
  choose edge hedge using hex
  have hinj : Function.Injective edge := by
    intro i j heq
    by_contra hn
    have hh := Finset.disjoint_left.mp (hd i j hn) (List.mem_toFinset.mpr (hedge i))
    apply hh
    rw [heq]
    exact List.mem_toFinset.mpr (hedge j)
  have hc := Fintype.card_le_of_injective edge hinj
  simpa using hc

private theorem paths_at_lam {n m : ℕ} (D : Fin m → Fin n × Fin n) (x y : Fin n)
    (hxy : x ≠ y) : HasDisjointPaths D (lam D x y) x y := by
  classical
  have hfinite : {k | HasDisjointPaths D k x y}.Finite := by
    apply (Set.finite_le_nat m).subset
    intro k hk
    exact path_count_bound D x y hxy k hk
  have hnonempty : {k | HasDisjointPaths D k x y}.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  exact hnonempty.csSup_mem hfinite

private theorem paths_mono {n m : ℕ} (D : Fin m → Fin n × Fin n) (x y : Fin n)
    {k l : ℕ} (hkl : k ≤ l) (h : HasDisjointPaths D l x y) : HasDisjointPaths D k x y := by
  obtain ⟨P, hP, hd⟩ := h
  refine ⟨fun i ↦ P (Fin.castLE hkl i), ?_, ?_⟩
  · intro i; exact hP _
  · intro i j hij
    apply hd
    intro he
    apply hij
    exact Fin.castLE_injective hkl he

theorem solution {n m : ℕ} (D : Fin m → Fin n × Fin n) (k : ℕ)
    (x y : Fin n) (hxy : x ≠ y)
    (h : ∀ S : Finset (Fin n), x ∈ S → y ∉ S → k ≤ outCount D S) :
    HasDisjointPaths D k x y := by
  have hmin := (sec2_maxflow_mincut D x y hxy).2
  obtain ⟨S, hS, hEq⟩ := hmin.1
  have hk : k ≤ lam D x y := by
    rw [← hEq]
    exact h S hS.1 hS.2
  exact paths_mono D x y hk (paths_at_lam D x y hxy)
