-- Prove2me | solution 1 for DiscreteConvex.IntegralConvexityB.theorem_3_13_tu_integral_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T00:33:35.705454+00:00
-- url     : https://prove2.me/submissions/86264536-525c-4061-9e9e-7e7c924b4b00

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsTotallyUnimodular
import Definitions.Def_DiscreteConvex_IntegralConvexityB_PrimalFeas
import Definitions.Def_DiscreteConvex_IntegralConvexityB_DualFeas



namespace DiscreteConvex.IntegralConvexityB

open Matrix

lemma tu_sq_rows {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (A : Matrix W V ℝ) {k : ℕ} (cs : Fin k → V)
    (hli : LinearIndependent ℝ (fun i : Fin k => fun w => A w (cs i))) :
    ∃ rs : Fin k → W, Function.Injective rs ∧ IsUnit (A.submatrix rs cs) := by
  set N : Matrix W (Fin k) ℝ := A.submatrix id cs with hN
  have h1 : N.transpose.rank = k := by
    rw [Matrix.rank_eq_finrank_span_row]
    have : N.transpose.row = (fun i : Fin k => fun w => A w (cs i)) := by
      funext i w; simp [hN, Matrix.row, Matrix.transpose]
    rw [this, finrank_span_eq_card hli, Fintype.card_fin]
  rw [Matrix.rank_transpose, Matrix.rank_eq_finrank_span_row] at h1
  have htop : Submodule.span ℝ (Set.range N.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [h1, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  obtain ⟨κ, a, ha, hspan, hli2⟩ := exists_linearIndependent' ℝ N.row
  have : Finite κ := Finite.of_injective a ha
  let _ : Fintype κ := Fintype.ofFinite κ
  have bs := Module.Basis.mk hli2 (by rw [hspan, htop])
  have hcard : Fintype.card κ = k := by
    have := Module.finrank_eq_card_basis bs
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    exact this.symm
  let e : κ ≃ Fin k := Fintype.equivFinOfCardEq hcard
  refine ⟨a ∘ e.symm, ha.comp e.symm.injective, ?_⟩
  rw [← Matrix.linearIndependent_rows_iff_isUnit]
  have : (A.submatrix (a ∘ e.symm) cs).row = (N.row ∘ a) ∘ e.symm := by
    funext i j; rfl
  rw [this]
  exact hli2.comp _ e.symm.injective

lemma tu_int_entry {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (A : Matrix W V ℝ) (hTU : IsTotallyUnimodular A) (w : W) (v : V) :
    ∃ z : ℤ, A w v = z := by
  have := hTU 1 (fun _ => w) (fun _ => v) (fun a b _ => Subsingleton.elim a b)
    (fun a b _ => Subsingleton.elim a b)
  simp only [Matrix.det_unique, Matrix.submatrix_apply] at this
  rcases this with h | h | h
  · exact ⟨0, by simp [h]⟩
  · exact ⟨1, by simp [h]⟩
  · exact ⟨-1, by simp [h]⟩

lemma tu_int_inv {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (A : Matrix W V ℝ) (hTU : IsTotallyUnimodular A) {k : ℕ} (rs : Fin k → W) (cs : Fin k → V)
    (hrs : Function.Injective rs) (hcs : Function.Injective cs)
    (hU : IsUnit (A.submatrix rs cs)) :
    ∃ Bi : Matrix (Fin k) (Fin k) ℤ, Bi.map (Int.cast : ℤ → ℝ) * A.submatrix rs cs = 1 ∧
      A.submatrix rs cs * Bi.map (Int.cast : ℤ → ℝ) = 1 := by
  choose Az hAz using tu_int_entry A hTU
  set Bz : Matrix (Fin k) (Fin k) ℤ := fun i j => Az (rs i) (cs j) with hBz
  have hB : A.submatrix rs cs = Bz.map (Int.cast : ℤ → ℝ) := by
    ext i j; rw [Matrix.submatrix_apply, Matrix.map_apply, hAz]
  have hdetR : (A.submatrix rs cs).det = ((Bz.det : ℤ) : ℝ) := by
    rw [hB]; exact (RingHom.map_det (Int.castRingHom ℝ) Bz).symm
  have hdet0 : (A.submatrix rs cs).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).mp hU |>.ne_zero
  have hunit : IsUnit Bz.det := by
    rcases hTU k rs cs hrs hcs with h | h | h
    · exact absurd h hdet0
    · rw [hdetR] at h
      have : Bz.det = 1 := by exact_mod_cast h
      rw [this]; exact isUnit_one
    · rw [hdetR] at h
      have : Bz.det = -1 := by exact_mod_cast h
      rw [this]; exact isUnit_one.neg
  refine ⟨Bz⁻¹, ?_, ?_⟩
  · have h := Matrix.map_mul (L := Bz⁻¹) (M := Bz) (f := Int.castRingHom ℝ)
    rw [Matrix.nonsing_inv_mul _ hunit, Int.coe_castRingHom] at h
    rw [hB, ← h]; simp
  · have h := Matrix.map_mul (L := Bz) (M := Bz⁻¹) (f := Int.castRingHom ℝ)
    rw [Matrix.mul_nonsing_inv _ hunit, Int.coe_castRingHom] at h
    rw [hB, ← h]; simp


lemma small_perturb {V : Type*} [Fintype V] (x d : V → ℝ) (hx : ∀ j, 0 ≤ x j)
    (hd : ∀ j, x j = 0 → d j = 0) :
    ∃ s > 0, ∀ j, 0 ≤ x j + s * d j ∧ 0 ≤ x j - s * d j := by
  classical
  by_cases hS : (Finset.univ.filter (fun j => x j ≠ 0)).Nonempty
  · set s := (Finset.univ.filter (fun j => x j ≠ 0)).inf' hS (fun j => x j / (|d j| + 1)) with hs
    have hpos : 0 < s := by
      rw [hs, Finset.lt_inf'_iff]
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have : 0 < x j := lt_of_le_of_ne (hx j) (Ne.symm hj)
      positivity
    refine ⟨s, hpos, fun j => ?_⟩
    by_cases hj : x j = 0
    · simp [hj, hd j hj]
    · have hle : s ≤ x j / (|d j| + 1) := Finset.inf'_le _ (by simp [hj])
      have h1 : 0 < |d j| + 1 := by positivity
      have h2 : s * (|d j| + 1) ≤ x j := by rwa [le_div_iff₀ h1] at hle
      have h3 : s * |d j| ≤ x j := by nlinarith
      have h4 : |s * d j| ≤ x j := by rw [abs_mul, abs_of_pos hpos]; exact h3
      constructor <;> linarith [abs_le.mp h4]
  · refine ⟨1, one_pos, fun j => ?_⟩
    have : x j = 0 := by
      by_contra h; exact hS ⟨j, by simp [h]⟩
    simp [this, hd j this]

lemma move_to_zero {V : Type*} [Fintype V] (x d : V → ℝ) (hx : ∀ j, 0 ≤ x j)
    (hneg : ∃ j, d j < 0) :
    ∃ t ≥ 0, (∀ j, 0 ≤ x j + t * d j) ∧ ∃ j, d j < 0 ∧ x j + t * d j = 0 := by
  classical
  have hN : (Finset.univ.filter (fun j => d j < 0)).Nonempty := by
    obtain ⟨j, hj⟩ := hneg; exact ⟨j, by simp [hj]⟩
  obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image _ (fun j => x j / (-d j)) hN
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj0 hmin
  have hpos0 : 0 < -d j0 := by linarith
  refine ⟨x j0 / (-d j0), div_nonneg (hx j0) hpos0.le, fun j => ?_, j0, hj0, ?_⟩
  · by_cases hj : d j < 0
    · have h := hmin j hj
      have hp : 0 < -d j := by linarith
      rw [div_le_div_iff₀ hpos0 hp] at h
      have : x j0 / -d j0 * d j = - (x j0 * (-d j)) / (-d j0) := by ring
      rw [this, add_div' _ _ _ hpos0.ne']
      apply div_nonneg _ hpos0.le
      nlinarith
    · push_neg at hj
      have := div_nonneg (hx j0) hpos0.le
      nlinarith [mul_nonneg this hj, hx j]
  · rw [show x j0 / -d j0 * d j0 = -(x j0 * (d j0 / d j0)) by ring, div_self hj0.ne]; ring

/-- reindex a sum over a finset `S` by `Fin S.card`. -/
lemma sum_reindex {V : Type*} [Fintype V] (S : Finset V) (f : V → ℝ)
    (hf : ∀ j, j ∉ S → f j = 0) :
    ∑ j, f j = ∑ i : Fin S.card, f (S.equivFin.symm i).val := by
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => hf j hj)]
  rw [← Finset.sum_coe_sort S f]
  exact (Equiv.sum_comp S.equivFin.symm (fun j => f j.val)).symm

lemma mapcast_mulVec {k : ℕ} (M : Matrix (Fin k) (Fin k) ℤ) (v : Fin k → ℤ) :
    (M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun i => (v i : ℝ)) = fun i => ((M *ᵥ v) i : ℝ) := by
  funext i; simp [Matrix.mulVec, dotProduct]

lemma primal_core {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (A : Matrix W V ℝ) (b : W → ℝ) (c : V → ℝ) (hTU : IsTotallyUnimodular A)
    (bz : W → ℤ) (hb : b = fun w => (bz w : ℝ))
    (x0 : V → ℝ) (hx0 : x0 ∈ PrimalFeas A b)
    (hopt0 : ∀ x' ∈ PrimalFeas A b, dotProduct c x0 ≤ dotProduct c x') :
    ∃ x ∈ PrimalFeas A b, (∃ xz : V → ℤ, x = fun v => (xz v : ℝ)) ∧
      ∀ x' ∈ PrimalFeas A b, dotProduct c x ≤ dotProduct c x' := by
  classical
  let supp : (V → ℝ) → Finset V := fun x => Finset.univ.filter (fun j => x j ≠ 0)
  have hex : ∃ n, ∃ x ∈ PrimalFeas A b, (∀ x' ∈ PrimalFeas A b, dotProduct c x ≤ dotProduct c x')
      ∧ (supp x).card = n := ⟨_, x0, hx0, hopt0, rfl⟩
  obtain ⟨x, hx, hopt, hcard⟩ := Nat.find_spec hex
  have hmin := fun m (hm : m < Nat.find hex) => Nat.find_min hex hm
  set S := supp x with hSdef
  have hxS : ∀ j, j ∉ S → x j = 0 := by
    intro j hj; by_contra h; exact hj (by simp [hSdef, supp, h])
  -- no kernel vector supported on S
  have hker : ∀ d : V → ℝ, (∀ j, j ∉ S → d j = 0) → A *ᵥ d = 0 → d = 0 := by
    intro d hdS hAd
    by_contra hd0
    -- c ⬝ d = 0
    obtain ⟨s, hs, hsj⟩ := small_perturb x d hx.2 (fun j hj => hdS j (by simp [hSdef, supp, hj]))
    have hfeas : ∀ t : ℝ, (∀ j, 0 ≤ x j + t * d j) → x + t • d ∈ PrimalFeas A b := by
      intro t ht
      refine ⟨?_, fun j => by simpa using ht j⟩
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hAd, smul_zero, add_zero, hx.1]
    have hcd : dotProduct c d = 0 := by
      have h1 := hopt _ (hfeas s (fun j => (hsj j).1))
      have h2 := hopt _ (hfeas (-s) (fun j => by have := (hsj j).2; linarith))
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at h1 h2
      nlinarith
    have key : ∀ d' : V → ℝ, (∀ j, j ∉ S → d' j = 0) → A *ᵥ d' = 0 → dotProduct c d' = 0 →
        (∃ j, d' j < 0) → False := by
      intro d' hdS' hAd' hcd' hneg
      obtain ⟨t, ht0, htj, j1, hj1, hj1z⟩ := move_to_zero x d' hx.2 hneg
      have hfeas' : x + t • d' ∈ PrimalFeas A b := by
        refine ⟨?_, fun j => by simpa using htj j⟩
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, hAd', smul_zero, add_zero, hx.1]
      have hopt' : ∀ x' ∈ PrimalFeas A b, dotProduct c (x + t • d') ≤ dotProduct c x' := by
        intro x' hx'
        rw [dotProduct_add, dotProduct_smul, hcd', smul_zero, add_zero]
        exact hopt x' hx'
      have hsub : supp (x + t • d') ⊆ S.erase j1 := by
        intro j hj
        simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul] at hj
        rw [Finset.mem_erase]
        refine ⟨fun h => hj (h ▸ hj1z), ?_⟩
        by_contra hjS
        exact hj (by rw [hxS j hjS, hdS' j hjS]; ring)
      have hj1S : j1 ∈ S := by
        by_contra h; have := hdS' j1 h; linarith
      have hlt : (supp (x + t • d')).card < Nat.find hex := by
        rw [← hcard]
        calc (supp (x + t • d')).card ≤ (S.erase j1).card := Finset.card_le_card hsub
          _ < S.card := Finset.card_erase_lt_of_mem hj1S
      exact hmin _ hlt ⟨_, hfeas', hopt', rfl⟩
    by_cases hneg : ∃ j, d j < 0
    · exact key d hdS hAd hcd hneg
    · push_neg at hneg
      have : ∃ j, d j ≠ 0 := by
        by_contra h; push_neg at h; exact hd0 (funext h)
      obtain ⟨j, hj⟩ := this
      refine key (-d) (fun j hj => by simp [hdS j hj]) (by rw [Matrix.mulVec_neg, hAd, neg_zero])
        (by rw [dotProduct_neg, hcd, neg_zero]) ⟨j, ?_⟩
      have := hneg j
      simp only [Pi.neg_apply]
      exact neg_neg_of_pos (lt_of_le_of_ne this (Ne.symm hj))
  -- columns indexed by S are linearly independent
  set k := S.card
  let cs : Fin k → V := fun i => (S.equivFin.symm i).val
  have hli : LinearIndependent ℝ (fun i : Fin k => fun w => A w (cs i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    let d : V → ℝ := fun j => if h : j ∈ S then g (S.equivFin ⟨j, h⟩) else 0
    have hdS : ∀ j, j ∉ S → d j = 0 := fun j hj => by simp [d, hj]
    have hdcs : ∀ i, d (cs i) = g i := by
      intro i
      simp only [d, cs, Finset.coe_mem, dif_pos, Subtype.coe_eta, Equiv.apply_symm_apply]
    have hAd : A *ᵥ d = 0 := by
      funext w
      have := congrFun hg w
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [sum_reindex S _ (fun j hj => by simp [hdS j hj])]
      rw [← this]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hdcs]; ring
    have := hker d hdS hAd
    intro i
    rw [← hdcs i, this]; rfl
  obtain ⟨rs, hrs, hU⟩ := tu_sq_rows A cs hli
  have hcs : Function.Injective cs := by
    intro i j h
    have : (S.equivFin.symm i) = (S.equivFin.symm j) := Subtype.ext h
    exact S.equivFin.symm.injective this
  obtain ⟨Bi, hBi1, -⟩ := tu_int_inv A hTU rs cs hrs hcs hU
  set xs : Fin k → ℝ := fun i => x (cs i)
  have hBx : A.submatrix rs cs *ᵥ xs = fun i => (bz (rs i) : ℝ) := by
    funext i
    have := congrFun hx.1 (rs i)
    rw [hb] at this
    simp only at this
    rw [← this]
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, xs]
    rw [sum_reindex S (fun j => A (rs i) j * x j) (fun j hj => by simp [hxS j hj])]
  have hxs : xs = fun i => (((Bi *ᵥ fun i => bz (rs i)) i : ℤ) : ℝ) := by
    have : xs = (Bi.map (Int.cast : ℤ → ℝ)) *ᵥ (A.submatrix rs cs *ᵥ xs) := by
      rw [Matrix.mulVec_mulVec, hBi1, Matrix.one_mulVec]
    rw [this, hBx, mapcast_mulVec]
  have hint : ∀ j, ∃ z : ℤ, x j = z := by
    intro j
    by_cases hj : j ∈ S
    · refine ⟨(Bi *ᵥ fun i => bz (rs i)) (S.equivFin ⟨j, hj⟩), ?_⟩
      have := congrFun hxs (S.equivFin ⟨j, hj⟩)
      simp only [xs, cs, Equiv.symm_apply_apply] at this
      exact this
    · exact ⟨0, by simp [hxS j hj]⟩
  choose xz hxz using hint
  exact ⟨x, hx, ⟨xz, funext hxz⟩, hopt⟩


lemma mapcast_vecMul {k : ℕ} (M : Matrix (Fin k) (Fin k) ℤ) (v : Fin k → ℤ) :
    vecMul (fun i => (v i : ℝ)) (M.map (Int.cast : ℤ → ℝ)) = fun i => ((vecMul v M) i : ℝ) := by
  funext i; simp [Matrix.vecMul, dotProduct]

lemma vecMul_move {V W : Type*} [Fintype V] [Fintype W] (A : Matrix W V ℝ) (y d : W → ℝ) (t : ℝ)
    (j : V) : vecMul (y + t • d) A j = vecMul y A j + t * vecMul d A j := by
  rw [Matrix.add_vecMul, Matrix.smul_vecMul]; rfl

lemma dual_core {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (A : Matrix W V ℝ) (b : W → ℝ) (c : V → ℝ) (hTU : IsTotallyUnimodular A)
    (cz : V → ℤ) (hc : c = fun v => (cz v : ℝ))
    (y0 : W → ℝ) (hy0 : y0 ∈ DualFeas A c)
    (hopt0 : ∀ y' ∈ DualFeas A c, dotProduct b y0 ≥ dotProduct b y') :
    ∃ y ∈ DualFeas A c, (∃ yz : W → ℤ, y = fun w => (yz w : ℝ)) ∧
      ∀ y' ∈ DualFeas A c, dotProduct b y ≥ dotProduct b y' := by
  classical
  let nt : (W → ℝ) → Finset V := fun y => Finset.univ.filter (fun j => vecMul y A j ≠ c j)
  have hex : ∃ n, ∃ y ∈ DualFeas A c, (∀ y' ∈ DualFeas A c, dotProduct b y ≥ dotProduct b y')
      ∧ (nt y).card = n := ⟨_, y0, hy0, hopt0, rfl⟩
  obtain ⟨y, hy, hopt, hcard⟩ := Nat.find_spec hex
  have hmin := fun m (hm : m < Nat.find hex) => Nat.find_min hex hm
  have hsl : ∀ j, 0 ≤ c j - vecMul y A j := fun j => by have := hy j; linarith
  have hker : ∀ d : W → ℝ, (∀ j, vecMul y A j = c j → vecMul d A j = 0) →
      ∀ j, vecMul d A j = 0 := by
    intro d hdT
    by_contra hne
    push_neg at hne
    obtain ⟨s, hs, hsj⟩ := small_perturb (fun j => c j - vecMul y A j) (fun j => vecMul d A j) hsl
      (fun j hj => hdT j (by linarith))
    have hfeas : ∀ t : ℝ, (∀ j, 0 ≤ c j - vecMul y A j - t * vecMul d A j) →
        y + t • d ∈ DualFeas A c := by
      intro t ht j
      rw [vecMul_move]; have := ht j; linarith
    have hbd : dotProduct b d = 0 := by
      have h1 := hopt _ (hfeas s (fun j => by have := (hsj j).2; linarith))
      have h2 := hopt _ (hfeas (-s) (fun j => by have := (hsj j).1; linarith))
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at h1 h2
      nlinarith
    have key : ∀ d' : W → ℝ, (∀ j, vecMul y A j = c j → vecMul d' A j = 0) →
        dotProduct b d' = 0 → (∃ j, 0 < vecMul d' A j) → False := by
      intro d' hdT' hbd' hpos
      obtain ⟨t, ht0, htj, j1, hj1, hj1z⟩ := move_to_zero (fun j => c j - vecMul y A j)
        (fun j => - vecMul d' A j) hsl (by obtain ⟨j, hj⟩ := hpos; exact ⟨j, by linarith⟩)
      have hfeas' : y + t • d' ∈ DualFeas A c := by
        intro j; rw [vecMul_move]; have := htj j; linarith
      have hopt' : ∀ y' ∈ DualFeas A c, dotProduct b (y + t • d') ≥ dotProduct b y' := by
        intro y' hy'
        rw [dotProduct_add, dotProduct_smul, hbd', smul_zero, add_zero]
        exact hopt y' hy'
      have hj1N : j1 ∈ nt y := by
        simp only [nt, Finset.mem_filter, Finset.mem_univ, true_and]
        intro h; have := hdT' j1 h; linarith
      have hsub : nt (y + t • d') ⊆ (nt y).erase j1 := by
        intro j hj
        simp only [nt, Finset.mem_filter, Finset.mem_univ, true_and, vecMul_move] at hj
        rw [Finset.mem_erase]
        refine ⟨fun h => hj (by subst h; linarith), ?_⟩
        simp only [nt, Finset.mem_filter, Finset.mem_univ, true_and]
        intro h; exact hj (by rw [hdT' j h, h]; ring)
      have hlt : (nt (y + t • d')).card < Nat.find hex := by
        rw [← hcard]
        calc (nt (y + t • d')).card ≤ ((nt y).erase j1).card := Finset.card_le_card hsub
          _ < (nt y).card := Finset.card_erase_lt_of_mem hj1N
      exact hmin _ hlt ⟨_, hfeas', hopt', rfl⟩
    obtain ⟨j, hj⟩ := hne
    rcases lt_or_gt_of_ne hj with h | h
    · refine key (-d) (fun j hj => by rw [Matrix.neg_vecMul]; simp [hdT j hj])
        (by rw [dotProduct_neg, hbd, neg_zero]) ⟨j, ?_⟩
      rw [Matrix.neg_vecMul]; simp only [Pi.neg_apply]; linarith
    · exact key d hdT hbd ⟨j, h⟩
  -- the tight columns
  set T : Finset V := Finset.univ.filter (fun j => vecMul y A j = c j) with hT
  let col : T → (W → ℝ) := fun j => fun w => A w j.val
  obtain ⟨κ, a, ha, hspan, hli2⟩ := exists_linearIndependent' ℝ col
  have : Finite κ := Finite.of_injective a ha
  let _ : Fintype κ := Fintype.ofFinite κ
  set k := Fintype.card κ
  let e : Fin k ≃ κ := (Fintype.equivFin κ).symm
  let cs : Fin k → V := fun i => (a (e i)).val
  have hli : LinearIndependent ℝ (fun i : Fin k => fun w => A w (cs i)) :=
    hli2.comp e e.injective
  have hcs : Function.Injective cs := by
    intro i j h
    exact e.injective (ha (Subtype.ext h))
  obtain ⟨rs, hrs, hU⟩ := tu_sq_rows A cs hli
  obtain ⟨Bi, hBi1, -⟩ := tu_int_inv A hTU rs cs hrs hcs hU
  set zz : Fin k → ℤ := vecMul (fun i => cz (cs i)) Bi
  let y' : W → ℝ := fun w => ∑ i, if rs i = w then (zz i : ℝ) else 0
  have hy'A : ∀ j, vecMul y' A j = ∑ i, (zz i : ℝ) * A (rs i) j := by
    intro j
    simp only [Matrix.vecMul, dotProduct, y', Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_ite_eq]; simp
  have hy'cs : ∀ i0, vecMul y' A (cs i0) = c (cs i0) := by
    intro i0
    rw [hy'A]
    have h1 : vecMul (fun i => (zz i : ℝ)) (A.submatrix rs cs) = fun i => c (cs i) := by
      have : (fun i => (zz i : ℝ)) = vecMul (fun i => (cz (cs i) : ℝ)) (Bi.map (Int.cast : ℤ → ℝ)) := by
        rw [mapcast_vecMul]
      rw [this, Matrix.vecMul_vecMul, hBi1, Matrix.vecMul_one, hc]
    have := congrFun h1 i0
    rw [← this]; rfl
  set dd := y' - y with hdd
  have hddT : ∀ j, vecMul y A j = c j → vecMul dd A j = 0 := by
    intro j hj
    let K : Submodule ℝ (W → ℝ) :=
      { carrier := {u | dotProduct dd u = 0}
        add_mem' := fun {u v} hu hv => by
          simp only [Set.mem_setOf_eq] at *; rw [dotProduct_add, hu, hv, add_zero]
        zero_mem' := by simp
        smul_mem' := fun r u hu => by
          simp only [Set.mem_setOf_eq] at *; rw [dotProduct_smul, hu, smul_zero] }
    have hle : Submodule.span ℝ (Set.range col) ≤ K := by
      rw [← hspan, Submodule.span_le]
      rintro _ ⟨κ', rfl⟩
      show dotProduct dd (fun w => A w (a κ').val) = 0
      have hk : κ' = e (e.symm κ') := (e.apply_symm_apply κ').symm
      rw [hk]
      show vecMul dd A (cs (e.symm κ')) = 0
      rw [hdd, Matrix.sub_vecMul, Pi.sub_apply, hy'cs]
      have hmem : cs (e.symm κ') ∈ T := (a (e (e.symm κ'))).2
      rw [hT, Finset.mem_filter] at hmem
      rw [hmem.2, sub_self]
    have hmem : col ⟨j, by rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hj⟩⟩ ∈ K :=
      hle (Submodule.subset_span ⟨_, rfl⟩)
    exact hmem
  have hddA := hker dd hddT
  have hy'eq : ∀ j, vecMul y' A j = vecMul y A j := by
    intro j
    have := hddA j
    rw [hdd, Matrix.sub_vecMul, Pi.sub_apply] at this
    linarith
  have hy'feas : y' ∈ DualFeas A c := fun j => by rw [hy'eq]; exact hy j
  have hymfeas : y - dd ∈ DualFeas A c := fun j => by
    rw [Matrix.sub_vecMul, Pi.sub_apply, hddA j, sub_zero]; exact hy j
  have hb1 := hopt _ hy'feas
  have hb2 := hopt _ hymfeas
  have hy'y : y' = y + dd := by rw [hdd]; abel
  rw [dotProduct_sub] at hb2
  rw [hy'y, dotProduct_add] at hb1
  refine ⟨y', hy'feas, ⟨fun w => ∑ i, if rs i = w then zz i else 0, ?_⟩, ?_⟩
  · funext w; simp only [y']; push_cast; rfl
  · intro y'' hy''
    have := hopt y'' hy''
    rw [hy'y, dotProduct_add]; linarith


theorem tu313_core {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V]
    [DecidableEq W] (A : Matrix W V ℝ) (b : W → ℝ) (c : V → ℝ)
    (hTU : IsTotallyUnimodular A) :
    ((∃ bz : W → ℤ, b = fun w => (bz w : ℝ)) →
        (∃ x0 ∈ PrimalFeas A b, ∀ x' ∈ PrimalFeas A b, dotProduct c x0 ≤ dotProduct c x') →
          ∃ x ∈ PrimalFeas A b, (∃ xz : V → ℤ, x = fun v => (xz v : ℝ)) ∧
            ∀ x' ∈ PrimalFeas A b, dotProduct c x ≤ dotProduct c x') ∧
      ((∃ cz : V → ℤ, c = fun v => (cz v : ℝ)) →
        (∃ y0 ∈ DualFeas A c, ∀ y' ∈ DualFeas A c, dotProduct b y0 ≥ dotProduct b y') →
          ∃ y ∈ DualFeas A c, (∃ yz : W → ℤ, y = fun w => (yz w : ℝ)) ∧
            ∀ y' ∈ DualFeas A c, dotProduct b y ≥ dotProduct b y') := by
  refine ⟨fun ⟨bz, hb⟩ ⟨x0, hx0, hopt⟩ => primal_core A b c hTU bz hb x0 hx0 hopt,
    fun ⟨cz, hc⟩ ⟨y0, hy0, hopt⟩ => dual_core A b c hTU cz hc y0 hy0 hopt⟩

end DiscreteConvex.IntegralConvexityB

open DiscreteConvex.IntegralConvexityB


theorem solution {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V]
    [DecidableEq W] (A : Matrix W V ℝ) (b : W → ℝ) (c : V → ℝ)
    (hTU : IsTotallyUnimodular A) :
    ((∃ bz : W → ℤ, b = fun w => (bz w : ℝ)) →
        (∃ x0 ∈ PrimalFeas A b, ∀ x' ∈ PrimalFeas A b, dotProduct c x0 ≤ dotProduct c x') →
          ∃ x ∈ PrimalFeas A b, (∃ xz : V → ℤ, x = fun v => (xz v : ℝ)) ∧
            ∀ x' ∈ PrimalFeas A b, dotProduct c x ≤ dotProduct c x') ∧
      ((∃ cz : V → ℤ, c = fun v => (cz v : ℝ)) →
        (∃ y0 ∈ DualFeas A c, ∀ y' ∈ DualFeas A c, dotProduct b y0 ≥ dotProduct b y') →
          ∃ y ∈ DualFeas A c, (∃ yz : W → ℤ, y = fun w => (yz w : ℝ)) ∧
            ∀ y' ∈ DualFeas A c, dotProduct b y ≥ dotProduct b y') := by
  exact tu313_core A b c hTU
