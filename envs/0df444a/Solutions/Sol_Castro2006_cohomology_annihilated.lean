-- Prove2me | solution 1 for Castro2006.cohomology_annihilated
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T15:50:17.639041+00:00
-- url     : https://prove2.me/submissions/2de3236d-b01d-4939-8f3e-e27d0b186f5a

import Mathlib
open CategoryTheory

/-!
Proposição 4.4.1(i): `|G|` annihilates `Hⁿ(G, A)` for `n ≥ 1`.

Classical cochain argument: for an inhomogeneous `(k+1)`-cocycle `f`, put
`h(g₀,…,g_{k-1}) = ∑_{s ∈ G} f(g₀,…,g_{k-1},s)`. Summing the cocycle identity
`(d f)(g₀,…,g_k,s) = 0` over `s` gives `d h + (-1)^(k+2) • |G| • f = 0`, so
`|G| • f = d((-1)^(k+1) • h)` is a coboundary.
-/

namespace Castro2006CohomologyAnnihilatedAux

variable {α : Type*}

lemma contractNth_castSucc_castSucc_snoc {k : ℕ} (op : α → α → α) (g : Fin (k + 1) → α) (s : α)
    (j : Fin k) :
    Fin.contractNth (Fin.castSucc (Fin.castSucc j)) op (Fin.snoc g s : Fin (k + 2) → α) =
      Fin.snoc (Fin.contractNth (Fin.castSucc j) op g) s := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp)]
    simp
  · rw [Fin.snoc_castSucc]
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using h),
        Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using h)]
      simp
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simpa using h),
        Fin.contractNth_apply_of_eq _ _ _ _ (by simpa using h)]
      rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using h),
        Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using h)]
      rw [Fin.succ_castSucc, Fin.snoc_castSucc]

lemma contractNth_castSucc_last_snoc {k : ℕ} (op : α → α → α) (g : Fin (k + 1) → α) (s : α) :
    Fin.contractNth (Fin.castSucc (Fin.last k)) op (Fin.snoc g s : Fin (k + 2) → α) =
      Fin.snoc (Fin.init g) (op (g (Fin.last k)) s) := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp)]
    simp
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]
    simp [Fin.init]

lemma contractNth_last_snoc {k : ℕ} (op : α → α → α) (g : Fin (k + 1) → α) (s : α) :
    Fin.contractNth (Fin.last (k + 1)) op (Fin.snoc g s : Fin (k + 2) → α) = g := by
  funext i
  rw [Fin.contractNth_apply_of_lt _ _ _ _ (by have := i.is_lt; simp; omega)]
  simp

lemma contractNth_last {k : ℕ} (op : α → α → α) (g : Fin (k + 1) → α) :
    Fin.contractNth (Fin.last k) op g = Fin.init g := by
  funext i
  rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]
  rfl

lemma snoc_succ {k : ℕ} (g : Fin (k + 1) → α) (s : α) :
    (fun i : Fin (k + 1) => (Fin.snoc g s : Fin (k + 2) → α) i.succ) =
      Fin.snoc (Fin.tail g) s := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp
  · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
    rfl

/-- The `Module ℤ` scalar action agrees with `zsmul`, stated in the form that appears
after unfolding the inhomogeneous differential. -/
lemma module_smul_eq_zsmul {M : Type*} [AddCommGroup M] (h : Module ℤ M) (n : ℤ) (x : M) :
    @HSMul.hSMul ℤ M M (@instHSMul ℤ M (@SMulZeroClass.toSMul ℤ M _
      (@DistribSMul.toSMulZeroClass ℤ M _
        (@DistribMulAction.toDistribSMul ℤ M _ _ h.toDistribMulAction)))) n x = n • x :=
  int_smul_eq_zsmul h n x

end Castro2006CohomologyAnnihilatedAux

open Castro2006CohomologyAnnihilatedAux groupCohomology in
theorem solution {G : Type} [Group G] [Fintype G] (A : Rep ℤ G) (n : ℕ) (hn : 1 ≤ n) :
    ∀ x : groupCohomology A n, (Fintype.card G : ℤ) • x = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  intro x
  induction x using groupCohomology_induction_on with
  | h z =>
  set f : (Fin (k + 1) → G) → A := iCocycles A (k + 1) z with hfdef
  have hf : ∀ g, (inhomogeneousCochains.d A (k + 1)).hom f g = 0 := by
    intro g
    have := ConcreteCategory.congr_hom ((inhomogeneousCochains A).iCycles_d (k + 1) (k + 1 + 1)) z
    have h2 := congrFun this g
    simp [CochainComplex.of_d] at h2
    exact h2
  -- `h' g = ∑ₛ f (g, s)`
  let h' : (Fin k → G) → A := fun g => ∑ s : G, f (Fin.snoc g s)
  have key : ∀ g, (inhomogeneousCochains.d A k).hom h' g +
      (-1 : ℤ) ^ (k + 2) • ((Fintype.card G : ℤ) • f g) = 0 := by
    intro g
    -- the cocycle identity at `(g₀, …, g_k, s)`
    have hs : ∀ s : G, A.ρ (g 0) (f (Fin.snoc (Fin.tail g) s)) +
        ((∑ j : Fin k, (-1 : ℤ) ^ ((j : ℕ) + 1) •
          f (Fin.snoc (Fin.contractNth (Fin.castSucc j) (· * ·) g) s)) +
        (-1 : ℤ) ^ (k + 1) • f (Fin.snoc (Fin.init g) (g (Fin.last k) * s)) +
        (-1 : ℤ) ^ (k + 1 + 1) • f g) = 0 := by
      intro s
      have := hf (Fin.snoc g s)
      rw [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at this
      simp only [contractNth_castSucc_castSucc_snoc, contractNth_castSucc_last_snoc,
        contractNth_last_snoc, snoc_succ, Fin.val_castSucc, Fin.val_last,
        module_smul_eq_zsmul] at this
      exact this
    -- sum it over `s ∈ G`
    have hsum := Finset.sum_eq_zero (s := Finset.univ) (fun s _ => hs s)
    simp only [Finset.sum_add_distrib, ← Finset.smul_sum, ← map_sum] at hsum
    rw [Finset.sum_comm] at hsum
    have hre : ∑ s : G, f (Fin.snoc (Fin.init g) (g (Fin.last k) * s)) = h' (Fin.init g) :=
      Fintype.sum_equiv (Equiv.mulLeft (g (Fin.last k))) _ _ (fun _ => rfl)
    rw [hre] at hsum
    rw [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_castSucc, contractNth_last]
    simp only [Fin.val_castSucc, Fin.val_last, Finset.sum_const, Finset.card_univ,
      module_smul_eq_zsmul] at hsum ⊢
    simp only [h', Finset.smul_sum, natCast_zsmul] at hsum ⊢
    rw [← hsum, add_assoc]
    rfl
  -- hence `|G| • z` is the coboundary of `(-1)^(k+1) • h'`
  have hz : (Fintype.card G : ℤ) • z = toCocycles A k (k + 1) ((-1 : ℤ) ^ (k + 1) • h') := by
    apply (ModuleCat.mono_iff_injective (iCocycles A (k + 1))).1 inferInstance
    have h1 := ConcreteCategory.congr_hom ((inhomogeneousCochains A).toCycles_i k (k + 1))
      ((-1 : ℤ) ^ (k + 1) • h')
    simp only [ConcreteCategory.comp_apply] at h1
    rw [h1, map_zsmul, ← hfdef, CochainComplex.of_d, map_zsmul]
    funext g
    have hε : (-1 : ℤ) ^ (k + 2) = -((-1) ^ (k + 1)) := by ring
    have hεε : (-1 : ℤ) ^ (k + 1) * (-1) ^ (k + 1) = 1 := by rw [← mul_pow]; norm_num
    have hD : (inhomogeneousCochains.d A k).hom h' g =
        (-1 : ℤ) ^ (k + 1) • ((Fintype.card G : ℤ) • f g) := by
      have := key g
      rw [hε, neg_smul, ← sub_eq_add_neg, sub_eq_zero] at this
      exact this
    rw [Pi.smul_apply, Pi.smul_apply]
    change _ = (-1 : ℤ) ^ (k + 1) • (inhomogeneousCochains.d A k).hom h' g
    rw [hD, smul_smul, hεε, one_smul]
  have h3 := ConcreteCategory.congr_hom
    ((inhomogeneousCochains A).toCycles_comp_homologyπ k (k + 1)) ((-1 : ℤ) ^ (k + 1) • h')
  simp only [ConcreteCategory.comp_apply] at h3
  rw [← map_zsmul, hz]
  exact h3
