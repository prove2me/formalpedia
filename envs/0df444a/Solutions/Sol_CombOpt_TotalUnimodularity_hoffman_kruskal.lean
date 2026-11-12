-- Prove2me | solution 1 for CombOpt.TotalUnimodularity.hoffman_kruskal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T21:33:54.361248+00:00
-- url     : https://prove2.me/submissions/0ffd3f0d-a120-480c-8ea2-a4a899f0ffb6

import Mathlib
import Definitions.Def_CombOpt_TotalUnimodularity_IsIntegralPolyhedron

set_option autoImplicit false

namespace HKAux

open Matrix

theorem rowL {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (x : Fin n → ℝ) (i : Fin m) :
    ((Matrix.fromRows A (-1 : Matrix (Fin n) (Fin n) ℤ)).map (Int.cast : ℤ → ℝ) *ᵥ x) (Sum.inl i)
      = (A.map (Int.cast : ℤ → ℝ) *ᵥ x) i := by
  simp [Matrix.mulVec, dotProduct]

theorem rowR {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (x : Fin n → ℝ) (j : Fin n) :
    ((Matrix.fromRows A (-1 : Matrix (Fin n) (Fin n) ℤ)).map (Int.cast : ℤ → ℝ) *ᵥ x) (Sum.inr j)
      = - x j := by
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

theorem memP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (x : Fin n → ℝ) :
    (A.map (Int.cast : ℤ → ℝ) *ᵥ x ≤ (fun i => (b i : ℝ)) ∧ 0 ≤ x) ↔
    ∀ r, ((Matrix.fromRows A (-1 : Matrix (Fin n) (Fin n) ℤ)).map (Int.cast : ℤ → ℝ) *ᵥ x) r
      ≤ ((Sum.elim b 0 r : ℤ) : ℝ) := by
  constructor
  · rintro ⟨hA, hx⟩ (i | j)
    · rw [rowL]; simpa using Pi.le_def.mp hA i
    · rw [rowR]; simpa using Pi.le_def.mp hx j
  · intro h
    refine ⟨Pi.le_def.mpr fun i => ?_, Pi.le_def.mpr fun j => ?_⟩
    · have := h (Sum.inl i); rw [rowL] at this; simpa using this
    · have := h (Sum.inr j); rw [rowR] at this; simpa using this

theorem integral_of_tight {n : ℕ} {κ : Type} [Fintype κ] (N : Matrix κ (Fin n) ℤ)
    (hN : N.IsTotallyUnimodular) (c : κ → ℤ) (x : Fin n → ℝ)
    (hx : N.map (Int.cast : ℤ → ℝ) *ᵥ x = fun r => (c r : ℝ))
    (hker : ∀ d : Fin n → ℝ, N.map (Int.cast : ℤ → ℝ) *ᵥ d = 0 → d = 0) :
    ∃ z : Fin n → ℤ, x = fun j => (z j : ℝ) := by
  classical
  set Nr := N.map (Int.cast : ℤ → ℝ) with hNr
  have hinj : Function.Injective Nr.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    exact hker d (by simpa using hd)
  have hrank : Nr.rank = n := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
  have hspan : Submodule.span ℝ (Set.range Nr.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, hrank, Module.finrank_fin_fun]
  obtain ⟨κ', a, ha, hsp, hli⟩ := exists_linearIndependent' (K := ℝ) Nr.row
  rw [hspan] at hsp
  have : Finite κ' := Finite.of_injective a ha
  let _ : Fintype κ' := Fintype.ofFinite κ'
  let bas : Module.Basis κ' ℝ (Fin n → ℝ) := Module.Basis.mk hli (by rw [hsp])
  have hcard : Fintype.card κ' = n := by
    have := Module.finrank_eq_card_basis bas
    rw [Module.finrank_fin_fun] at this
    exact this.symm
  let e : Fin n ≃ κ' := (Fintype.equivFinOfCardEq hcard).symm
  let f : Fin n → κ := a ∘ e
  have hf : Function.Injective f := ha.comp e.injective
  set Bz : Matrix (Fin n) (Fin n) ℤ := N.submatrix f id with hBz
  set B : Matrix (Fin n) (Fin n) ℝ := Bz.map (Int.cast : ℤ → ℝ) with hB
  have hBrow : B.row = (Nr.row ∘ a) ∘ e := by
    funext i j; simp [hB, hBz, hNr, f, Matrix.row, Function.comp_apply]; rfl
  have hBunit : IsUnit B := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit, hBrow]
    exact hli.comp e e.injective
  have hdetB : B.det = (Bz.det : ℝ) := by
    have := (Int.castRingHom ℝ).map_det Bz
    simpa [hB] using this.symm
  have hdet0 : (Bz.det : ℝ) ≠ 0 := by
    rw [← hdetB]; exact (Matrix.isUnit_iff_isUnit_det B).mp hBunit |>.ne_zero
  have hsq : (Bz.det : ℝ) * Bz.det = 1 := by
    obtain ⟨s, hs⟩ := hN n f id hf Function.injective_id
    have hs' : Bz.det = s := hs.symm
    rw [hs'] at hdet0 ⊢
    rcases s with _ | _ | _ <;> simp at hdet0 ⊢
  have hBx : B *ᵥ x = fun i => (c (f i) : ℝ) := by
    funext i
    have := congrFun hx (f i)
    simpa [hB, hBz, hNr, Matrix.mulVec, dotProduct] using this
  have key : B.det • x = B.adjugate *ᵥ (fun i => (c (f i) : ℝ)) := by
    rw [← hBx, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have hadj : B.adjugate = Bz.adjugate.map (Int.cast : ℤ → ℝ) := by
    have := (Int.castRingHom ℝ).map_adjugate Bz
    simpa [hB] using this.symm
  refine ⟨fun j => Bz.det * (Bz.adjugate *ᵥ (fun i => c (f i))) j, ?_⟩
  funext j
  have hj := congrFun key j
  simp only [Pi.smul_apply, smul_eq_mul, hadj, hdetB] at hj
  have h2 : ((Bz.adjugate *ᵥ (fun i => c (f i))) j : ℝ)
      = (Bz.adjugate.map (Int.cast : ℤ → ℝ) *ᵥ fun i => (c (f i) : ℝ)) j := by
    simp [Matrix.mulVec, dotProduct]
  show x j = ((Bz.det * (Bz.adjugate *ᵥ (fun i => c (f i))) j : ℤ) : ℝ)
  rw [Int.cast_mul, h2, ← hj]
  linear_combination (-(x j)) * hsq

set_option maxHeartbeats 1000000 in
theorem core {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι (Fin n) ℤ)
    (hM : M.IsTotallyUnimodular) (c : ι → ℤ)
    (hpt : ∀ d : Fin n → ℝ, d ≠ 0 → ∃ r, (M.map (Int.cast : ℤ → ℝ) *ᵥ d) r ≠ 0)
    (F : Set (Fin n → ℝ))
    (hFP : ∀ x ∈ F, ∀ r, (M.map (Int.cast : ℤ → ℝ) *ᵥ x) r ≤ c r)
    (hE : ∀ x ∈ F, ∀ s : Fin n → ℝ, ∀ l μ : ℝ, 0 < l → 0 < μ →
      (∀ r, (M.map (Int.cast : ℤ → ℝ) *ᵥ (x + l • s)) r ≤ c r) →
      (∀ r, (M.map (Int.cast : ℤ → ℝ) *ᵥ (x - μ • s)) r ≤ c r) → x + l • s ∈ F)
    (hne : F.Nonempty) : ∃ z : Fin n → ℤ, (fun j => (z j : ℝ)) ∈ F := by
  classical
  set Mr := M.map (Int.cast : ℤ → ℝ) with hMr
  let T : (Fin n → ℝ) → Finset ι := fun y => Finset.univ.filter (fun r => (Mr *ᵥ y) r = c r)
  have hmemT : ∀ y r, r ∈ T y ↔ (Mr *ᵥ y) r = c r := by
    intro y r; simp [T]
  obtain ⟨x, hxF, hxmax⟩ : ∃ x ∈ F, ∀ y ∈ F, (T y).card ≤ (T x).card := by
    let S : Finset ℕ :=
      (Finset.range (Fintype.card ι + 1)).filter (fun k => ∃ y ∈ F, (T y).card = k)
    obtain ⟨y0, hy0⟩ := hne
    have hSne : S.Nonempty := ⟨(T y0).card, by
      simp only [S, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le (Finset.card_le_univ _), y0, hy0, rfl⟩⟩
    obtain ⟨-, x, hxF, hx⟩ := Finset.mem_filter.mp (S.max'_mem hSne)
    refine ⟨x, hxF, fun y hy => ?_⟩
    rw [hx]
    apply S.le_max'
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Finset.card_le_univ _), y, hy, rfl⟩
  have hxP := hFP x hxF
  have hMy : ∀ (s : Fin n → ℝ) (μ : ℝ) r,
      (Mr *ᵥ (x + μ • s)) r = (Mr *ᵥ x) r + μ * (Mr *ᵥ s) r := by
    intro s μ r; simp [Matrix.mulVec_add, Matrix.mulVec_smul]
  have hMy' : ∀ (s : Fin n → ℝ) (μ : ℝ) r,
      (Mr *ᵥ (x - μ • s)) r = (Mr *ᵥ x) r - μ * (Mr *ᵥ s) r := by
    intro s μ r; simp [Matrix.mulVec_sub, Matrix.mulVec_smul]
  have hker : ∀ d : Fin n → ℝ, (∀ r ∈ T x, (Mr *ᵥ d) r = 0) → d = 0 := by
    intro d hd
    by_contra hd0
    obtain ⟨r0, hr0⟩ := hpt d hd0
    obtain ⟨s, hs0, hsT⟩ : ∃ s : Fin n → ℝ, 0 < (Mr *ᵥ s) r0 ∧ ∀ r ∈ T x, (Mr *ᵥ s) r = 0 := by
      rcases lt_or_gt_of_ne hr0 with h | h
      · refine ⟨-d, ?_, ?_⟩
        · rw [Matrix.mulVec_neg, Pi.neg_apply]; linarith
        · intro r hr; rw [Matrix.mulVec_neg, Pi.neg_apply, hd r hr, neg_zero]
      · exact ⟨d, h, hd⟩
    let U := Finset.univ.filter (fun r => 0 < (Mr *ᵥ s) r)
    have hr0U : r0 ∈ U := by simp [U, hs0]
    let ratio : ι → ℝ := fun r => (c r - (Mr *ᵥ x) r) / (Mr *ᵥ s) r
    obtain ⟨r1, hr1U, hr1min⟩ := Finset.exists_min_image U ratio ⟨r0, hr0U⟩
    have hr1pos : 0 < (Mr *ᵥ s) r1 := (Finset.mem_filter.mp hr1U).2
    have hr1T : r1 ∉ T x := fun h => (ne_of_gt hr1pos) (hsT r1 h)
    have hslack1 : 0 < (c r1 : ℝ) - (Mr *ᵥ x) r1 := by
      have h2 : (Mr *ᵥ x) r1 ≠ c r1 := fun h => hr1T ((hmemT x r1).mpr h)
      exact sub_pos.mpr (lt_of_le_of_ne (hxP r1) h2)
    obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (c r1 - (Mr *ᵥ x) r1) / (Mr *ᵥ s) r1 := ⟨_, rfl⟩
    have hlpos : 0 < l := by rw [hl]; exact div_pos hslack1 hr1pos
    have hyP : ∀ r, (Mr *ᵥ (x + l • s)) r ≤ c r := by
      intro r
      rw [hMy]
      by_cases hrU : r ∈ U
      · have hpos : 0 < (Mr *ᵥ s) r := (Finset.mem_filter.mp hrU).2
        have h4 : l ≤ (c r - (Mr *ᵥ x) r) / (Mr *ᵥ s) r := by rw [hl]; exact hr1min r hrU
        have h3 : l * (Mr *ᵥ s) r ≤ c r - (Mr *ᵥ x) r := (le_div_iff₀ hpos).mp h4
        linarith
      · have hneg : (Mr *ᵥ s) r ≤ 0 := by
          simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hrU; exact hrU
        have := hxP r
        nlinarith
    obtain ⟨μ, hμpos, hμP⟩ : ∃ μ : ℝ, 0 < μ ∧ ∀ r, (Mr *ᵥ (x - μ • s)) r ≤ c r := by
      have hev : ∀ r, ∀ᶠ μ in nhds (0:ℝ), (Mr *ᵥ x) r - μ * (Mr *ᵥ s) r ≤ c r := by
        intro r
        by_cases hrT : r ∈ T x
        · refine Filter.Eventually.of_forall (fun μ => ?_)
          rw [hsT r hrT, mul_zero, sub_zero]; exact hxP r
        · have hlt : (Mr *ᵥ x) r < c r :=
            lt_of_le_of_ne (hxP r) (fun h => hrT ((hmemT x r).mpr h))
          have hcont : Continuous fun μ : ℝ => (Mr *ᵥ x) r - μ * (Mr *ᵥ s) r := by fun_prop
          have h0 : (fun μ : ℝ => (Mr *ᵥ x) r - μ * (Mr *ᵥ s) r) 0 < c r := by simpa using hlt
          exact ((hcont.tendsto 0).eventually (Iio_mem_nhds h0)).mono (fun μ hμ => le_of_lt hμ)
      have hall : ∀ᶠ μ in nhdsWithin (0:ℝ) (Set.Ioi 0),
          ∀ r, (Mr *ᵥ x) r - μ * (Mr *ᵥ s) r ≤ c r :=
        (Filter.eventually_all.mpr hev).filter_mono nhdsWithin_le_nhds
      obtain ⟨μ, hμ, hμpos⟩ := (hall.and self_mem_nhdsWithin).exists
      exact ⟨μ, hμpos, fun r => by rw [hMy']; exact hμ r⟩
    have hyF := hE x hxF s l μ hlpos hμpos hyP hμP
    have hsub : T x ⊂ T (x + l • s) := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨r1, ?_, hr1T⟩
        rw [hmemT, hMy]
        have : l * (Mr *ᵥ s) r1 = c r1 - (Mr *ᵥ x) r1 := by
          rw [hl]; exact div_mul_cancel₀ _ (ne_of_gt hr1pos)
        linarith
      · intro r hr
        rw [hmemT] at hr ⊢
        rw [hMy, hsT r ((hmemT x r).mpr hr), mul_zero, add_zero]; exact hr
    have h5 := hxmax _ hyF
    have h6 := Finset.card_lt_card hsub
    omega
  let N : Matrix (T x) (Fin n) ℤ := M.submatrix (Subtype.val) id
  have hN1 : N.map (Int.cast : ℤ → ℝ) *ᵥ x = fun r => ((c r.1 : ℤ) : ℝ) := by
    funext r
    have := (hmemT x r.1).mp r.2
    simpa [N, hMr, Matrix.mulVec, dotProduct] using this
  have hN2 : ∀ d : Fin n → ℝ, N.map (Int.cast : ℤ → ℝ) *ᵥ d = 0 → d = 0 := by
    intro d hd; apply hker d; intro r hr
    have := congrFun hd ⟨r, hr⟩
    simpa [N, hMr, Matrix.mulVec, dotProduct] using this
  obtain ⟨z, hz⟩ := integral_of_tight N (hM.submatrix _ _) (fun r => c r.1) x hN1 hN2
  exact ⟨z, hz ▸ hxF⟩

theorem backward {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : A.IsTotallyUnimodular)
    (b : Fin m → ℤ) :
    CombOpt.TotalUnimodularity.IsIntegralPolyhedron
        {x : Fin n → ℝ | A.map (Int.cast : ℤ → ℝ) *ᵥ x ≤ (fun i => (b i : ℝ)) ∧ 0 ≤ x} := by
  classical
  intro F hF hne
  set P := {x : Fin n → ℝ | A.map (Int.cast : ℤ → ℝ) *ᵥ x ≤ (fun i => (b i : ℝ)) ∧ 0 ≤ x}
    with hP
  have hmem : ∀ x, x ∈ P ↔ ∀ r, ((Matrix.fromRows A (-1 : Matrix (Fin n) (Fin n) ℤ)).map
      (Int.cast : ℤ → ℝ) *ᵥ x) r ≤ ((Sum.elim b 0 r : ℤ) : ℝ) := fun x => memP A b x
  have hTU : (Matrix.fromRows A (-1 : Matrix (Fin n) (Fin n) ℤ)).IsTotallyUnimodular := by
    refine hA.fromRows_unitlike (fun _ i => ⟨i, -1, ?_⟩)
    funext j
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  have hpt : ∀ d : Fin n → ℝ, d ≠ 0 → ∃ r, ((Matrix.fromRows A (-1 : Matrix (Fin n) (Fin n) ℤ)).map
      (Int.cast : ℤ → ℝ) *ᵥ d) r ≠ 0 := by
    intro d hd
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hd
    refine ⟨Sum.inr j, ?_⟩
    rw [rowR]; simpa using hj
  rcases hF with hF | hF | ⟨w, t, hw, hval, -, hF⟩
  · rw [hF] at hne; exact absurd hne Set.not_nonempty_empty
  · apply core _ hTU (Sum.elim b 0) hpt F
    · intro x hx r; rw [hF] at hx; exact (hmem x).mp hx r
    · intro x _ s l μ _ _ h1 _; rw [hF]; exact (hmem _).mpr h1
    · exact hne
  · apply core _ hTU (Sum.elim b 0) hpt F
    · intro x hx r; rw [hF] at hx; exact (hmem x).mp hx.1 r
    · intro x hx s l μ hl hμ h1 h2
      rw [hF] at hx ⊢
      have hP1 := (hmem _).mpr h1
      have hP2 := (hmem _).mpr h2
      have e1 := hval _ hP1
      have e2 := hval _ hP2
      have hx2 : w ⬝ᵥ x = t := hx.2
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at e1
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul] at e2
      have hws : w ⬝ᵥ s = 0 := by
        rcases lt_trichotomy (w ⬝ᵥ s) 0 with h | h | h
        · nlinarith
        · exact h
        · nlinarith
      refine ⟨hP1, ?_⟩
      show w ⬝ᵥ (x + l • s) = t
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hws, mul_zero, add_zero, hx2]
    · exact hne

theorem sum_extend {k n : ℕ} (g : Fin k → Fin n) (hg : g.Injective) (a : Fin n → ℝ)
    (v : Fin k → ℝ) :
    ∑ j, a j * Function.extend g v 0 j = ∑ i, a (g i) * v i := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨g, hg⟩))]
  · simp [Finset.sum_map, hg.extend_apply]
  · intro j _ hj
    have hj' : ¬ ∃ i, g i = j := by simpa using hj
    simp [Function.extend_apply' _ _ _ hj']

set_option maxHeartbeats 1000000 in
theorem forward {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : ∀ b : Fin m → ℤ, CombOpt.TotalUnimodularity.IsIntegralPolyhedron
        {x : Fin n → ℝ | A.map (Int.cast : ℤ → ℝ) *ᵥ x ≤ (fun i => (b i : ℝ)) ∧ 0 ≤ x}) :
    A.IsTotallyUnimodular := by
  classical
  intro k f g hf hg
  set Bz : Matrix (Fin k) (Fin k) ℤ := A.submatrix f g with hBz
  set B : Matrix (Fin k) (Fin k) ℝ := Bz.map (Int.cast : ℤ → ℝ) with hB
  have hdetB : B.det = (Bz.det : ℝ) := by
    have := (Int.castRingHom ℝ).map_det Bz
    simpa [hB] using this.symm
  by_cases h0 : Bz.det = 0
  · exact ⟨0, by simp [h0]⟩
  have hBdet : B.det ≠ 0 := by rw [hdetB]; exact_mod_cast h0
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet
  have hcol : ∀ l : Fin k, ∃ q : Fin k → ℤ, B *ᵥ (fun i => (q i : ℝ)) = Pi.single l 1 := by
    intro l
    obtain ⟨u, hu⟩ : ∃ u : Fin k → ℝ, u = B⁻¹ *ᵥ Pi.single l 1 := ⟨_, rfl⟩
    have hBu' : B *ᵥ u = Pi.single l 1 := by
      rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hBu, Matrix.one_mulVec]
    let y : Fin k → ℤ := fun i => ⌈- u i⌉
    let v : Fin k → ℝ := fun i => (y i : ℝ) + u i
    have hv0 : ∀ i, 0 ≤ v i := fun i => by
      have := Int.le_ceil (-u i); simp only [v, y]; linarith
    have hBv : ∀ i, (B *ᵥ v) i = ((Bz *ᵥ y) i : ℝ) + (((Pi.single l (1:ℤ) : Fin k → ℤ) i : ℤ) : ℝ) := by
      intro i
      have hvv : v = (fun i => (y i : ℝ)) + u := rfl
      rw [hvv, Matrix.mulVec_add, Pi.add_apply, hBu']
      congr 1
      · simp [hB, Matrix.mulVec, dotProduct]
      · by_cases h : i = l
        · subst h; simp
        · simp [h]
    obtain ⟨x, hx⟩ : ∃ x : Fin n → ℝ, x = Function.extend g v 0 := ⟨_, rfl⟩
    have hAx : ∀ i, (A.map (Int.cast : ℤ → ℝ) *ᵥ x) (f i) = (B *ᵥ v) i := by
      intro i
      rw [hx]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
      rw [sum_extend g hg]
      simp [hB, hBz]
    obtain ⟨bb, hbb⟩ : ∃ bb : Fin m → ℤ, bb = Function.extend f
        (fun i => (Bz *ᵥ y) i + (Pi.single l (1:ℤ) : Fin k → ℤ) i)
        (fun r => ⌈(A.map (Int.cast : ℤ → ℝ) *ᵥ x) r⌉) := ⟨_, rfl⟩
    set P := {x : Fin n → ℝ | A.map (Int.cast : ℤ → ℝ) *ᵥ x ≤ (fun i => (bb i : ℝ)) ∧ 0 ≤ x}
      with hP
    have hrow : ∀ i, (A.map (Int.cast : ℤ → ℝ) *ᵥ x) (f i) = (bb (f i) : ℝ) := by
      intro i; rw [hAx, hBv, hbb, hf.extend_apply]; push_cast; ring
    have hxP : x ∈ P := by
      refine ⟨Pi.le_def.mpr fun r => ?_, Pi.le_def.mpr fun j => ?_⟩
      · by_cases hr : ∃ i, f i = r
        · obtain ⟨i, rfl⟩ := hr; exact le_of_eq (hrow i)
        · show _ ≤ ((bb r : ℤ) : ℝ)
          rw [hbb, Function.extend_apply' _ _ _ hr]; exact Int.le_ceil _
      · show (0:ℝ) ≤ x j
        by_cases hj : ∃ i, g i = j
        · obtain ⟨i, rfl⟩ := hj; rw [hx, hg.extend_apply]; exact hv0 i
        · rw [hx, Function.extend_apply' _ _ _ hj]; simp
    let δ : Fin n → ℝ := fun j => if ∃ i, g i = j then 0 else 1
    let w : Fin n → ℝ := fun j => (∑ i, (A (f i) j : ℝ)) - δ j
    let t : ℝ := ∑ i, (bb (f i) : ℝ)
    have hwdot : ∀ z : Fin n → ℝ,
        w ⬝ᵥ z = ∑ i, (A.map (Int.cast : ℤ → ℝ) *ᵥ z) (f i) - ∑ j, δ j * z j := by
      intro z
      simp only [w, dotProduct, Matrix.mulVec, Matrix.map_apply, sub_mul,
        Finset.sum_sub_distrib, Finset.sum_mul]
      rw [Finset.sum_comm]
    have hgap : ∀ z : Fin n → ℝ, t - w ⬝ᵥ z = ∑ i, ((bb (f i) : ℝ)
        - (A.map (Int.cast : ℤ → ℝ) *ᵥ z) (f i)) + ∑ j, δ j * z j := by
      intro z; rw [hwdot]; simp only [t, Finset.sum_sub_distrib]; ring
    have hδz : ∀ z ∈ P, ∀ j, 0 ≤ δ j * z j := by
      intro z hz j
      apply mul_nonneg
      · simp only [δ]; split_ifs <;> norm_num
      · exact Pi.le_def.mp hz.2 j
    have hrz : ∀ z ∈ P, ∀ i, 0 ≤ (bb (f i) : ℝ) - (A.map (Int.cast : ℤ → ℝ) *ᵥ z) (f i) := by
      intro z hz i; exact sub_nonneg.mpr (Pi.le_def.mp hz.1 (f i))
    have hval : ∀ z ∈ P, w ⬝ᵥ z ≤ t := by
      intro z hz
      have := hgap z
      have h1 := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hrz z hz i)
      have h2 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hδz z hz j)
      linarith
    have hxt : w ⬝ᵥ x = t := by
      have := hgap x
      have h1 : ∑ i, ((bb (f i) : ℝ) - (A.map (Int.cast : ℤ → ℝ) *ᵥ x) (f i)) = 0 :=
        Finset.sum_eq_zero (fun i _ => by rw [hrow]; ring)
      have h2 : ∑ j, δ j * x j = 0 := Finset.sum_eq_zero (fun j _ => by
        by_cases hj : ∃ i, g i = j
        · simp [δ, hj]
        · rw [hx, Function.extend_apply' _ _ _ hj]; simp)
      linarith
    have huniq : ∀ z ∈ P, w ⬝ᵥ z = t → z = x := by
      intro z hz hzt
      have hg0 := hgap z
      rw [hzt, sub_self] at hg0
      have h1 := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hrz z hz i)
      have h2 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hδz z hz j)
      have e1 : ∑ i, ((bb (f i) : ℝ) - (A.map (Int.cast : ℤ → ℝ) *ᵥ z) (f i)) = 0 := by
        linarith
      have e2 : ∑ j, δ j * z j = 0 := by linarith
      have t1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hrz z hz i)).mp e1
      have t2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hδz z hz j)).mp e2
      have hzoff : ∀ j, ¬ (∃ i, g i = j) → z j = 0 := by
        intro j hj; have := t2 j (Finset.mem_univ _); simpa [δ, hj] using this
      have hzext : z = Function.extend g (fun i => z (g i)) 0 := by
        funext j
        by_cases hj : ∃ i, g i = j
        · obtain ⟨i, rfl⟩ := hj; rw [hg.extend_apply]
        · rw [Function.extend_apply' _ _ _ hj, hzoff j hj]; rfl
      have hBz' : B *ᵥ (fun i => z (g i)) = B *ᵥ v := by
        funext i
        have := t1 i (Finset.mem_univ _)
        have hA' : (A.map (Int.cast : ℤ → ℝ) *ᵥ z) (f i) = (B *ᵥ fun i => z (g i)) i := by
          conv_lhs => rw [hzext]
          simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
          rw [sum_extend g hg]
          simp [hB, hBz]
        rw [← hAx, ← hA', hrow]; linarith
      have hv : (fun i => z (g i)) = v := by
        have := congrArg (fun q => B⁻¹ *ᵥ q) hBz'
        simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hBu] using this
      rw [hzext, hv, hx]
    let F : Set (Fin n → ℝ) := P ∩ {z | w ⬝ᵥ z = t}
    have hFne : F.Nonempty := ⟨x, hxP, hxt⟩
    have hFace : CombOpt.TotalUnimodularity.IsFace P F := by
      by_cases hw : w = 0
      · right; left
        ext z; constructor
        · exact fun hz => hz.1
        · intro hz; refine ⟨hz, ?_⟩
          show w ⬝ᵥ z = t
          rw [← hxt, hw, zero_dotProduct, zero_dotProduct]
      · right; right
        exact ⟨w, t, hw, hval, hFne, rfl⟩
    obtain ⟨zz, hzz⟩ := hA bb F hFace hFne
    have hzx := huniq _ hzz.1 hzz.2
    refine ⟨fun i => zz (g i) - y i, ?_⟩
    have hvint : ∀ i, v i = (zz (g i) : ℝ) := by
      intro i; have := congrFun hzx (g i); rw [hx, hg.extend_apply] at this; exact this.symm
    have hq : (fun i => ((zz (g i) - y i : ℤ) : ℝ)) = u := by
      funext i; push_cast; rw [← hvint]; simp [v]
    rw [hq, hBu']
  choose q hq using hcol
  let Q : Matrix (Fin k) (Fin k) ℤ := Matrix.of fun i l => q l i
  have hBQ : B * Q.map (Int.cast : ℤ → ℝ) = 1 := by
    ext i l
    have := congrFun (hq l) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, Q, Matrix.of_apply]
    rw [this]
    by_cases h : i = l
    · subst h; simp
    · simp [h, Matrix.one_apply]
  have hdetQ : (Q.map (Int.cast : ℤ → ℝ)).det = (Q.det : ℝ) := by
    have := (Int.castRingHom ℝ).map_det Q
    simpa using this.symm
  have h1 : ((Bz.det * Q.det : ℤ) : ℝ) = 1 := by
    have := congrArg Matrix.det hBQ
    rw [Matrix.det_mul, Matrix.det_one, hdetB, hdetQ] at this
    rw [Int.cast_mul]; exact this
  have h2 : Bz.det * Q.det = 1 := by exact_mod_cast h1
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h2 with h | h
  · exact ⟨1, by simp [h]⟩
  · exact ⟨-1, by simp [h]⟩

end HKAux

open CombOpt.TotalUnimodularity Matrix in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    (∀ b : Fin m → ℤ, IsIntegralPolyhedron
        {x : Fin n → ℝ | A.map (Int.cast : ℤ → ℝ) *ᵥ x ≤ (fun i => (b i : ℝ)) ∧ 0 ≤ x}) ↔
      A.IsTotallyUnimodular := by
  constructor
  · exact HKAux.forward A
  · exact fun h b => HKAux.backward A h b
