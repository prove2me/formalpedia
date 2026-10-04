-- Prove2me | solution 1 for ClassicalSchur.not_coveredBySumFree_Icc_of_triangleRamsey
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-04T00:31:00.744813+00:00
-- url     : https://prove2.me/submissions/0113b55a-7abd-4317-a27d-efdda6bdeacf

-- Generated from lean/ClassicalSchur/SchurBound.lean
--   imports : 0 platform node(s), 2 definition bundle(s)
--   inlined : 0 file-scoped / sub-threshold helper(s)
--   rename  : not_coveredBySumFree_Icc_of_triangleRamsey -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurRamsey
import Mathlib



open ClassicalSchur in
theorem solution {k r : ℕ} (hR : TriangleRamsey k r) :
    ¬ CoveredBySumFree (Set.Icc 1 (2 * ((k + 1) * ((r - 1) / 2) + 1))) (k + 1) := by
  classical
  rintro ⟨C, hC, hcov⟩
  set q := (r - 1) / 2 with hq
  set h := (k + 1) * q + 1 with hh
  -- a cover set for every element of `[1, 2h]`
  have hmem : ∀ n : ℕ, ∃ t : Fin (k + 1), 1 ≤ n → n ≤ 2 * h → n ∈ C t := by
    intro n
    by_cases hn : 1 ≤ n ∧ n ≤ 2 * h
    · obtain ⟨t, ht⟩ := Set.mem_iUnion.mp (hcov ⟨hn.1, hn.2⟩)
      exact ⟨t, fun _ _ => ht⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hn⟩
  choose f hf using hmem
  -- one cover set holds `q + 1` elements of `[1, h]`
  have hmaps : ∀ a ∈ Finset.Icc 1 h, f a ∈ (Finset.univ : Finset (Fin (k + 1))) :=
    fun a _ => Finset.mem_univ _
  have hlt : (Finset.univ : Finset (Fin (k + 1))).card * q < (Finset.Icc 1 h).card := by
    rw [Finset.card_univ, Fintype.card_fin, Nat.card_Icc]
    omega
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt
  set A := (Finset.Icc 1 h).filter fun a => f a = i with hA
  have hAC : ∀ a ∈ A, 1 ≤ a ∧ a ≤ h ∧ a ∈ C i := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha1
    refine ⟨h1, h2, ?_⟩
    have := hf a h1 (by omega)
    rwa [ha2] at this
  -- the points `h ± a`
  set V := A.image (fun a => h - a) ∪ A.image (fun a => h + a) with hV
  have hinj1 : Set.InjOn (fun a => h - a) A := by
    intro a ha b hb hab
    have hab' : h - a = h - b := hab
    have := hAC a ha
    have := hAC b hb
    omega
  have hinj2 : Set.InjOn (fun a => h + a) A := by
    intro a _ b _ hab
    have hab' : h + a = h + b := hab
    omega
  have hdisj : Disjoint (A.image (fun a => h - a)) (A.image (fun a => h + a)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx1
    obtain ⟨b, hb, hbx⟩ := Finset.mem_image.mp hx2
    have hax' : h - a = x := hax
    have hbx' : h + b = x := hbx
    have := hAC a ha
    have := hAC b hb
    omega
  have hVcard : 2 * A.card ≤ V.card := by
    rw [hV, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj1,
      Finset.card_image_of_injOn hinj2]
    omega
  have hVmem : ∀ x ∈ V, (∃ a ∈ A, x = h - a) ∨ (∃ a ∈ A, x = h + a) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
      exact Or.inl ⟨a, ha, hax.symm⟩
    · obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
      exact Or.inr ⟨a, ha, hax.symm⟩
  have hV2h : ∀ x ∈ V, x ≤ 2 * h := by
    intro x hx
    rcases hVmem x hx with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · omega
    · have := hAC a ha
      omega
  -- no difference of two points is in `C i`
  have hnoti : ∀ x ∈ V, ∀ y ∈ V, x < y → y - x ∉ C i := by
    intro x hx y hy hxy hyx
    rcases hVmem x hx with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;>
      rcases hVmem y hy with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
    · obtain ⟨-, ha2, haC⟩ := hAC a ha
      obtain ⟨-, hb2, hbC⟩ := hAC b hb
      have e : h - b - (h - a) + b = a := by omega
      exact hC i _ hyx _ hbC (by rw [e]; exact haC)
    · obtain ⟨-, ha2, haC⟩ := hAC a ha
      obtain ⟨-, -, hbC⟩ := hAC b hb
      have e : h + b - (h - a) = a + b := by omega
      exact hC i a haC b hbC (by rw [← e]; exact hyx)
    · omega
    · obtain ⟨-, -, haC⟩ := hAC a ha
      obtain ⟨-, -, hbC⟩ := hAC b hb
      have e : h + b - (h + a) + a = b := by omega
      exact hC i _ hyx _ haC (by rw [e]; exact hbC)
  -- colour the pairs of `V` by the cover set of the difference
  set K := (Finset.univ.image fun j : Fin (k + 1) => (j : ℕ)).erase (i : ℕ) with hK
  have hKcard : K.card ≤ k := by
    have h1 : (Finset.univ.image fun j : Fin (k + 1) => (j : ℕ)).card ≤ k + 1 :=
      Finset.card_image_le.trans (by simp)
    have h2 : (i : ℕ) ∈ Finset.univ.image fun j : Fin (k + 1) => (j : ℕ) :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rw [hK, Finset.card_erase_of_mem h2]
    omega
  have hcolK : ∀ x ∈ V, ∀ y ∈ V, x < y → (f (y - x) : ℕ) ∈ K := by
    intro x hx y hy hxy
    rw [hK, Finset.mem_erase]
    refine ⟨fun heq => ?_, Finset.mem_image.mpr ⟨f (y - x), Finset.mem_univ _, rfl⟩⟩
    have hfi : f (y - x) = i := Fin.ext heq
    have hy2 := hV2h y hy
    have hmemf := hf (y - x) (by omega) (by omega)
    rw [hfi] at hmemf
    exact hnoti x hx y hy hxy hmemf
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, h1, h2⟩ :=
    hR V K (fun x y => (f (y - x) : ℕ)) hKcard (by omega) hcolK
  -- a monochromatic triangle is a Schur triple in one cover set
  have e1 : f (y - x) = f (z - y) := Fin.ext h1
  have e2 : f (y - x) = f (z - x) := Fin.ext h2
  have hz2 := hV2h z hz
  have m1 := hf (y - x) (by omega) (by omega)
  have m2 := hf (z - y) (by omega) (by omega)
  have m3 := hf (z - x) (by omega) (by omega)
  rw [← e1] at m2
  rw [← e2] at m3
  exact hC (f (y - x)) _ m1 _ m2 (by rw [show y - x + (z - y) = z - x by omega]; exact m3)
