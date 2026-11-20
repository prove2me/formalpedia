-- Prove2me | solution 1 for BlockSSM.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-20T01:06:44.286183+00:00
-- url     : https://prove2.me/submissions/b4fb431e-c9d9-4535-88c9-75f94c67dbcc

import Mathlib
import Definitions.Def_BlockSSM_trackerDim
import Definitions.Def_BlockSSM_coverDim

universe u

namespace BlockSSM_Proof

open BlockSSM

/-! ### Part 0: Word & Tracker Preliminaries -/

section WordPrelims

variable {G : Type u} [Group G] {b : ℕ∞}

@[simp]
lemma wordProd_nil : wordProd ([] : List G) = 1 := by
  simp [wordProd]

lemma wordProd_append (s₁ s₂ : List G) :
    wordProd (s₁ ++ s₂) = wordProd s₂ * wordProd s₁ := by
  simp [wordProd, List.reverse_append, List.prod_append]

@[simp]
lemma wordProd_singleton (g : G) : wordProd [g] = g := by
  simp [wordProd]

@[simp]
lemma wordMap_nil (T : Tracker G b) (h : State T.n) :
    T.wordMap [] h = h := rfl

lemma wordMap_append (T : Tracker G b) (s₁ s₂ : List G) (h : State T.n) :
    T.wordMap (s₁ ++ s₂) h = T.wordMap s₂ (T.wordMap s₁ h) := by
  simp [Tracker.wordMap, List.foldl_append]

@[simp]
lemma wordMap_singleton (T : Tracker G b) (g : G) (h : State T.n) :
    T.wordMap [g] h = T.step g h := rfl

/-- Single-block step map of a tracker. -/
def blockStep (T : Tracker G b) (i : Fin T.m) (g : G) (x : Fin (T.n i) → ℂ) :
    Fin (T.n i) → ℂ :=
  (T.A g i).mulVec x + T.c g i

/-- Single-block word map of a tracker. -/
def blockWordMap (T : Tracker G b) (i : Fin T.m) (s : List G) (x : Fin (T.n i) → ℂ) :
    Fin (T.n i) → ℂ :=
  s.foldl (fun y g => blockStep T i g y) x

lemma wordMap_apply (T : Tracker G b) (s : List G) (h : State T.n) (i : Fin T.m) :
    T.wordMap s h i = blockWordMap T i s (h i) := by
  induction s generalizing h with
  | nil => rfl
  | cons g s ih =>
    simpa [Tracker.wordMap, blockWordMap, Tracker.step, blockStep] using ih (T.step g h)

@[simp]
lemma blockWordMap_nil (T : Tracker G b) (i : Fin T.m) (x : Fin (T.n i) → ℂ) :
    blockWordMap T i [] x = x := rfl

lemma blockWordMap_append (T : Tracker G b) (i : Fin T.m) (s₁ s₂ : List G)
    (x : Fin (T.n i) → ℂ) :
    blockWordMap T i (s₁ ++ s₂) x = blockWordMap T i s₂ (blockWordMap T i s₁ x) := by
  simp [blockWordMap, List.foldl_append]

/-- Cumulative linear transition matrix on block `i` along word `s`. -/
def blockMat (T : Tracker G b) (i : Fin T.m) (s : List G) :
    Matrix (Fin (T.n i)) (Fin (T.n i)) ℂ :=
  s.foldl (fun M g => T.A g i * M) 1

lemma blockWordMap_sub (T : Tracker G b) (i : Fin T.m) (s : List G)
    (x y : Fin (T.n i) → ℂ) :
    blockWordMap T i s x - blockWordMap T i s y = (blockMat T i s).mulVec (x - y) := by
  induction s using List.reverseRecOn with
  | nil =>
    simp [blockWordMap, blockMat]
  | append_singleton s g ih =>
    simp only [blockWordMap, blockMat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change blockStep T i g (blockWordMap T i s x) - blockStep T i g (blockWordMap T i s y) =
      (T.A g i * blockMat T i s).mulVec (x - y)
    dsimp [blockStep]
    have hsub :
        ((T.A g i).mulVec (blockWordMap T i s x) + T.c g i) -
          ((T.A g i).mulVec (blockWordMap T i s y) + T.c g i) =
        (T.A g i).mulVec (blockWordMap T i s x - blockWordMap T i s y) := by
      rw [add_sub_add_right_eq_sub, ← Matrix.mulVec_sub]
    rw [hsub, ih, Matrix.mulVec_mulVec]

end WordPrelims

/-! ### Part 1: Representation & Subrepresentation Transport Helpers -/

section RepHelpers

variable {H : Type*} [Group H]

lemma subrep_ext {V : Type*} [AddCommMonoid V] [Module ℂ V] {ρ : Representation ℂ H V}
    {W₁ W₂ : Subrepresentation ρ} (h : W₁.toSubmodule = W₂.toSubmodule) : W₁ = W₂ := by
  cases W₁; cases W₂; cases h; rfl

/-- An `H`-equivariant `ℂ`-linear equivalence induces an order isomorphism of subrepresentations. -/
def subrepOrderIso {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂]
    {σ₁ : Representation ℂ H V₁} {σ₂ : Representation ℂ H V₂}
    (e : V₁ ≃ₗ[ℂ] V₂) (he : ∀ g v, e (σ₁ g v) = σ₂ g (e v)) :
    Subrepresentation σ₁ ≃o Subrepresentation σ₂ where
  toFun W :=
    { toSubmodule := W.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule := by
        intro g y hy
        rcases hy with ⟨x, hx, rfl⟩
        refine ⟨σ₁ g x, W.apply_mem_toSubmodule g hx, ?_⟩
        change e (σ₁ g x) = σ₂ g (e x)
        exact he g x }
  invFun W :=
    { toSubmodule := W.toSubmodule.map e.symm.toLinearMap
      apply_mem_toSubmodule := by
        intro g x hx
        rcases hx with ⟨y, hy, rfl⟩
        refine ⟨σ₂ g y, W.apply_mem_toSubmodule g hy, ?_⟩
        apply e.injective
        simp [he] }
  left_inv W := by
    apply subrep_ext
    ext x
    simp
  right_inv W := by
    apply subrep_ext
    ext y
    simp
  map_rel_iff' := by
    intro W₁ W₂
    change W₁.toSubmodule.map e.toLinearMap ≤ W₂.toSubmodule.map e.toLinearMap ↔
      W₁.toSubmodule ≤ W₂.toSubmodule
    constructor
    · intro h x hx
      rcases h ⟨x, hx, rfl⟩ with ⟨x', hx', hxx'⟩
      have : x' = x := e.injective hxx'
      simpa [this] using hx'
    · exact Submodule.map_mono

lemma isIrreducible_iff_of_equiv {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂]
    {σ₁ : Representation ℂ H V₁} {σ₂ : Representation ℂ H V₂}
    (e : V₁ ≃ₗ[ℂ] V₂) (he : ∀ g v, e (σ₁ g v) = σ₂ g (e v)) :
    σ₁.IsIrreducible ↔ σ₂.IsIrreducible := by
  unfold Representation.IsIrreducible
  exact OrderIso.isSimpleOrder_iff (subrepOrderIso e he)

/-- Push a subrepresentation of `W₀.toRepresentation` forward to a subrepresentation of `ρ`. -/
def liftSubrep {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ H V}
    (W₀ : Subrepresentation ρ) (U : Subrepresentation W₀.toRepresentation) :
    Subrepresentation ρ where
  toSubmodule := U.toSubmodule.map W₀.toSubmodule.subtype
  apply_mem_toSubmodule := by
    intro g v hv
    rcases hv with ⟨u, hu, rfl⟩
    exact ⟨W₀.toRepresentation g u, U.apply_mem_toSubmodule g hu, rfl⟩

lemma liftSubrep_equiv_irrep {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ H V}
    (W₀ : Subrepresentation ρ) (U : Subrepresentation W₀.toRepresentation) :
    (U.toRepresentation.IsIrreducible ↔ (liftSubrep W₀ U).toRepresentation.IsIrreducible) ∧
      Module.finrank ℂ U.toSubmodule = Module.finrank ℂ (liftSubrep W₀ U).toSubmodule := by
  let eU : U.toSubmodule ≃ₗ[ℂ] (liftSubrep W₀ U).toSubmodule :=
    U.toSubmodule.equivMapOfInjective W₀.toSubmodule.subtype W₀.toSubmodule.injective_subtype
  have heU : ∀ g x, eU (U.toRepresentation g x) = (liftSubrep W₀ U).toRepresentation g (eU x) := by
    intro g x
    ext
    rfl
  exact ⟨isIrreducible_iff_of_equiv eU heU, eU.finrank_eq⟩

lemma irrepDegreesLE_subrep {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ H V}
    {b : ℕ∞} (hρ : IrrepDegreesLE ρ b) (W₀ : Subrepresentation ρ) :
    IrrepDegreesLE W₀.toRepresentation b := by
  intro U hU
  obtain ⟨hirr, hdim⟩ := liftSubrep_equiv_irrep W₀ U
  rw [hdim]
  exact hρ (liftSubrep W₀ U) (hirr.mp hU)

lemma irrepDegreesLE_of_equiv {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂]
    {σ₁ : Representation ℂ H V₁} {σ₂ : Representation ℂ H V₂} {b : ℕ∞}
    (e : V₁ ≃ₗ[ℂ] V₂) (he : ∀ g v, e (σ₁ g v) = σ₂ g (e v))
    (h₁ : IrrepDegreesLE σ₁ b) : IrrepDegreesLE σ₂ b := by
  intro W₂ hW₂
  let W₁ := (subrepOrderIso e he).symm W₂
  let eW : W₁.toSubmodule ≃ₗ[ℂ] W₂.toSubmodule :=
    { toFun := fun x =>
        ⟨e x.1, by
          rcases x.2 with ⟨y, hy, hyx⟩
          have hx_eq : e x.1 = y := by rw [← hyx]; simp
          rwa [hx_eq]⟩
      map_add' := fun x₁ x₂ => Subtype.ext (map_add e x₁.1 x₂.1)
      map_smul' := fun c x => Subtype.ext (map_smul e c x.1)
      invFun := fun y => ⟨e.symm y.1, ⟨y.1, y.2, rfl⟩⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1) }
  have heW : ∀ g x, eW (W₁.toRepresentation g x) = W₂.toRepresentation g (eW x) := by
    intro g x
    exact Subtype.ext (he g x.1)
  have hW₁ : W₁.toRepresentation.IsIrreducible :=
    (isIrreducible_iff_of_equiv eW heW).mpr hW₂
  rw [← eW.finrank_eq]
  exact h₁ W₁ hW₁

end RepHelpers

/-! ### Part 2: Direction 1 (`trackerDim G b ≤ coverDim G b`) -/

section UpperBound

/-- A `ℂ`-vector space is never covered by finitely many proper `ℂ`-subspaces. -/
lemma exists_notMem_of_finite_subspaces {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} [Finite ι] (W : ι → Submodule ℂ V) (hW : ∀ i, W i ≠ ⊤) :
    ∃ v : V, ∀ i, v ∉ W i := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  suffices ∀ s : Finset ι, (∀ i ∈ s, W i ≠ ⊤) → ∃ v : V, ∀ i ∈ s, v ∉ W i by
    rcases this Finset.univ (fun i _ => hW i) with ⟨v, hv⟩
    exact ⟨v, fun i => hv i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨0, by simp⟩
  | @insert a s' ha ih =>
    intro hs
    obtain ⟨u, hu⟩ := ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
    have hWa : ∃ w : V, w ∉ W a := by
      by_contra h_all
      push_neg at h_all
      exact hs a (Finset.mem_insert_self a s') (Submodule.eq_top_iff'.mpr h_all)
    rcases hWa with ⟨w, hw⟩
    by_contra h_cov
    push_neg at h_cov
    let s := insert a s'
    have hchoose : ∀ k : Fin (s.card + 1), ∃ j : s, u + (k.1 : ℂ) • w ∈ W j.1 := by
      intro k
      rcases h_cov (u + (k.1 : ℂ) • w) with ⟨j, hj, hmem⟩
      exact ⟨⟨j, hj⟩, hmem⟩
    choose f hf using hchoose
    have hcard : Fintype.card s < Fintype.card (Fin (s.card + 1)) := by
      simp
    obtain ⟨k₁, k₂, hk_ne, hfk⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
    let j := (f k₁).1
    have hj_mem : j ∈ s := (f k₁).2
    have hm₁ : u + (k₁.1 : ℂ) • w ∈ W j := hf k₁
    have hm₂ : u + (k₂.1 : ℂ) • w ∈ W j := by
      have := hf k₂
      rwa [← hfk] at this
    have hdiff : ((k₁.1 : ℂ) - (k₂.1 : ℂ)) • w ∈ W j := by
      have hsub := Submodule.sub_mem (W j) hm₁ hm₂
      have heq : (u + (k₁.1 : ℂ) • w) - (u + (k₂.1 : ℂ) • w) =
          ((k₁.1 : ℂ) - (k₂.1 : ℂ)) • w := by
        rw [sub_smul]
        abel
      rwa [heq] at hsub
    have hc_ne : (k₁.1 : ℂ) - (k₂.1 : ℂ) ≠ 0 := by
      intro h0
      have : (k₁.1 : ℂ) = (k₂.1 : ℂ) := sub_eq_zero.mp h0
      exact hk_ne (Fin.ext (Nat.cast_injective this))
    have hw_j : w ∈ W j := by
      simpa [inv_smul_smul₀ hc_ne] using Submodule.smul_mem (W j) ((k₁.1 : ℂ) - (k₂.1 : ℂ))⁻¹ hdiff
    have hj_ne_a : j ≠ a := by
      intro hja
      rw [hja] at hw_j
      exact hw hw_j
    have hj_s' : j ∈ s' := Finset.mem_of_mem_insert_of_ne hj_mem hj_ne_a
    have hu_j : u ∈ W j := by
      have hkw : (k₁.1 : ℂ) • w ∈ W j := Submodule.smul_mem (W j) (k₁.1 : ℂ) hw_j
      have := Submodule.sub_mem (W j) hm₁ hkw
      simpa using this
    exact hu j hj_s' hu_j

/-- Every faithful representation of a finite group over `ℂ` admits a vector with trivial
stabilizer. -/
lemma exists_injective_orbit {H V : Type*} [Group H] [Finite H]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (hρ : Function.Injective ρ) :
    ∃ v₀ : V, Function.Injective (fun x : H => ρ x v₀) := by
  let W : {x : H // x ≠ 1} → Submodule ℂ V :=
    fun x => LinearMap.ker (ρ x.1 - LinearMap.id)
  have hW : ∀ x : {x : H // x ≠ 1}, W x ≠ ⊤ := by
    intro x htop
    apply x.2
    apply hρ
    ext v
    have hv : v ∈ W x := by rw [htop]; trivial
    have hsub : ρ x.1 v - v = 0 := by simpa [W] using hv
    rw [map_one]
    change ρ x.1 v = v
    exact sub_eq_zero.mp hsub
  obtain ⟨v₀, hv₀⟩ := exists_notMem_of_finite_subspaces W hW
  refine ⟨v₀, ?_⟩
  intro x y hxy
  dsimp at hxy
  by_contra hne
  have hne1 : y⁻¹ * x ≠ 1 := by
    intro h1
    exact hne (inv_mul_eq_one.mp h1).symm
  have hfix : ρ (y⁻¹ * x) v₀ = v₀ := by
    calc
      ρ (y⁻¹ * x) v₀ = ρ y⁻¹ (ρ x v₀) := by simp [map_mul]
      _ = ρ y⁻¹ (ρ y v₀) := by rw [hxy]
      _ = ρ (y⁻¹ * y) v₀ := by simp [map_mul]
      _ = v₀ := by simp
  apply hv₀ ⟨y⁻¹ * x, hne1⟩
  change ρ (y⁻¹ * x) v₀ - v₀ = 0
  rw [hfix, sub_self]

/-- Maschke's theorem directly on `Subrepresentation ρ`: every subrepresentation over `ℂ` of a
finite group admits a complementary subrepresentation. -/
lemma exists_isCompl_subrep {H V : Type*} [Group H] [Finite H]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ H V} (W : Subrepresentation ρ) :
    ∃ K : Subrepresentation ρ, IsCompl W.toSubmodule K.toSubmodule := by
  haveI : Fintype H := Fintype.ofFinite H
  obtain ⟨Q₀, hQ₀⟩ := Submodule.exists_isCompl W.toSubmodule
  let p₀ : V →ₗ[ℂ] V := W.toSubmodule.subtype.comp (W.toSubmodule.linearProjOfIsCompl Q₀ hQ₀)
  have hp₀_mem : ∀ v, p₀ v ∈ W.toSubmodule := fun v => (W.toSubmodule.linearProjOfIsCompl Q₀ hQ₀ v).2
  have hp₀_id : ∀ w ∈ W.toSubmodule, p₀ w = w := by
    intro w hw
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hQ₀ ⟨w, hw⟩)
  let p : V →ₗ[ℂ] V := (Fintype.card H : ℂ)⁻¹ • ∑ x : H, (ρ x⁻¹).comp (p₀.comp (ρ x))
  have hp_mem : ∀ v, p v ∈ W.toSubmodule := by
    intro v
    simp only [p, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    refine Submodule.smul_mem W.toSubmodule _ (Submodule.sum_mem W.toSubmodule ?_)
    intro x _
    exact W.apply_mem_toSubmodule x⁻¹ (hp₀_mem (ρ x v))
  have hp_id : ∀ w ∈ W.toSubmodule, p w = w := by
    intro w hw
    simp only [p, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    have hterm : ∀ x : H, ρ x⁻¹ (p₀ (ρ x w)) = w := by
      intro x
      rw [hp₀_id (ρ x w) (W.apply_mem_toSubmodule x hw)]
      calc
        ρ x⁻¹ (ρ x w) = ρ (x⁻¹ * x) w := by simp [map_mul]
        _ = w := by simp
    simp_rw [hterm, Finset.sum_const, Finset.card_univ]
    have hcard_ne : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hcard_ne]
  have hp_equiv : ∀ (g : H) (v : V), p (ρ g v) = ρ g (p v) := by
    intro g v
    simp only [p, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ ?_
    intro x
    dsimp [Equiv.mulRight]
    have hmul : ρ x (ρ g v) = ρ (x * g) v := by
      rw [map_mul]
      rfl
    have hinv : x⁻¹ = g * (x * g)⁻¹ := by group
    rw [hmul, hinv, map_mul]
    rfl
  let K : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker p
      apply_mem_toSubmodule := by
        intro g v hv
        change p (ρ g v) = 0
        rw [hp_equiv, hv, map_zero] }
  refine ⟨K, IsCompl.of_eq ?_ ?_⟩
  · ext v
    simp only [Submodule.mem_inf, Submodule.mem_bot, K, LinearMap.mem_ker]
    constructor
    · rintro ⟨hvW, hpv⟩
      rw [← hp_id v hvW, hpv]
    · rintro rfl
      exact ⟨W.toSubmodule.zero_mem, map_zero p⟩
  · ext v
    simp only [Submodule.mem_top, iff_true]
    rw [Submodule.mem_sup]
    refine ⟨p v, hp_mem v, v - p v, ?_, add_sub_cancel _ _⟩
    change p (v - p v) = 0
    rw [map_sub, hp_id (p v) (hp_mem v), sub_self]

/-- Splitting `State (@Fin.cases m' (fun _ => ℕ) n₀ n')` into block `0` and the remaining blocks. -/
def stateConsEquiv {m' : ℕ} (n₀ : ℕ) (n' : Fin m' → ℕ) :
    State (@Fin.cases m' (fun _ => ℕ) n₀ n') ≃ₗ[ℂ] (Fin n₀ → ℂ) × State n' where
  toFun u := (u 0, fun j => u j.succ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun q := @Fin.cases m' (fun i => Fin (@Fin.cases m' (fun _ => ℕ) n₀ n' i) → ℂ) q.1 q.2
  left_inv u := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j; rfl
  right_inv q := by
    ext <;> rfl

/-- Maschke block-diagonalization: any finite-dimensional complex `H`-representation with
irreducible subrepresentations of degree `≤ b` is block-diagonalizable with block sizes `≤ b`. -/
lemma exists_block_diag {H : Type*} [Group H] [Finite H] (b : ℕ∞) :
    ∀ (k : ℕ) (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (hk : Module.finrank ℂ V = k) (ρ : Representation ℂ H V) (_ : IrrepDegreesLE ρ b),
      ∃ (m : ℕ) (n : Fin m → ℕ) (_ : ∀ i, (n i : ℕ∞) ≤ b)
        (e : State n ≃ₗ[ℂ] V) (M : H → ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ),
        (∑ i, n i = k) ∧
        ∀ (x : H) (u : State n), e (fun i => (M x i).mulVec (u i)) = ρ x (e u) := by
  classical
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro V _ _ _ hk ρ hirr
    by_cases hk0 : k = 0
    · subst hk0
      have hbot_top : (⊥ : Submodule ℂ V) = ⊤ :=
        Submodule.eq_of_le_of_finrank_le bot_le (by simp [hk])
      have hsub : Subsingleton V :=
        ⟨fun x y => by
          have hx : x ∈ (⊥ : Submodule ℂ V) := by rw [hbot_top]; trivial
          have hy : y ∈ (⊥ : Submodule ℂ V) := by rw [hbot_top]; trivial
          rw [Submodule.mem_bot] at hx hy
          rw [hx, hy]⟩
      refine ⟨0, Fin.elim0, fun i => i.elim0,
        { toFun := fun _ => 0
          map_add' := fun _ _ => by simp
          map_smul' := fun _ _ => by simp
          invFun := fun _ i => i.elim0
          left_inv := fun u => by funext i; exact i.elim0
          right_inv := fun v => Subsingleton.elim _ _ },
        fun _ i => i.elim0, by simp, ?_⟩
      intro x u
      exact Subsingleton.elim _ _
    · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
      have htop_ne : (⊤ : Subrepresentation ρ).toSubmodule ≠ ⊥ := by
        intro hbot
        have : Module.finrank ℂ (⊤ : Submodule ℂ V) = 0 := by
          change Module.finrank ℂ (⊤ : Subrepresentation ρ).toSubmodule = 0
          rw [hbot, finrank_bot]
        rw [finrank_top, hk] at this
        exact hk0 this
      have hex : ∃ r : ℕ, ∃ W : Subrepresentation ρ,
          W.toSubmodule ≠ ⊥ ∧ Module.finrank ℂ W.toSubmodule = r :=
        ⟨k, ⊤, htop_ne, by change Module.finrank ℂ (⊤ : Submodule ℂ V) = k; rw [finrank_top, hk]⟩
      let n₀ : ℕ := Nat.find hex
      obtain ⟨W₀, hW₀_ne, hW₀_dim⟩ := Nat.find_spec hex
      have hW₀_n₀ : Module.finrank ℂ W₀.toSubmodule = n₀ := hW₀_dim
      have hn₀_pos : 0 < n₀ := by
        by_contra hn₀0
        have hn₀_eq : n₀ = 0 := Nat.eq_zero_of_not_pos hn₀0
        have hdim0 : Module.finrank ℂ W₀.toSubmodule = 0 := hW₀_n₀.trans hn₀_eq
        exact hW₀_ne ((Submodule.finrank_eq_zero).mp hdim0)
      have hW₀_irr : W₀.toRepresentation.IsIrreducible := by
        unfold Representation.IsIrreducible
        have : Nontrivial (Subrepresentation W₀.toRepresentation) := by
          refine ⟨⟨⊥, ⊤, ?_⟩⟩
          intro hbt
          apply hW₀_ne
          ext v
          simp only [Submodule.mem_bot]
          constructor
          · intro hv
            have hmem_top : (⟨v, hv⟩ : W₀.toSubmodule) ∈ (⊤ : Subrepresentation W₀.toRepresentation).toSubmodule := trivial
            rw [← hbt] at hmem_top
            have h0 : (⟨v, hv⟩ : W₀.toSubmodule) = 0 := hmem_top
            exact congrArg Subtype.val h0
          · rintro rfl; exact W₀.toSubmodule.zero_mem
        refine IsSimpleOrder.mk ?_
        intro U
        by_cases hU : U.toSubmodule = ⊥
        · left
          exact subrep_ext hU
        · right
          let U' := liftSubrep W₀ U
          have hU'_ne : U'.toSubmodule ≠ ⊥ := by
            intro hbot
            apply hU
            ext u
            simp only [Submodule.mem_bot]
            constructor
            · intro hu
              have : (u : V) ∈ U'.toSubmodule := ⟨u, hu, rfl⟩
              rw [hbot] at this
              exact Subtype.ext this
            · rintro rfl; exact U.toSubmodule.zero_mem
          have hmin : n₀ ≤ Module.finrank ℂ U'.toSubmodule :=
            Nat.find_min' hex ⟨U', hU'_ne, rfl⟩
          have hU'_le : U'.toSubmodule ≤ W₀.toSubmodule := by
            rintro v ⟨u, _, rfl⟩
            exact u.2
          have hU'_eq : U'.toSubmodule = W₀.toSubmodule :=
            Submodule.eq_of_le_of_finrank_le hU'_le (by rw [hW₀_n₀]; exact hmin)
          apply subrep_ext
          change U.toSubmodule = ⊤
          rw [eq_top_iff]
          intro u _
          have huV : (u : V) ∈ U'.toSubmodule := by rw [hU'_eq]; exact u.2
          rcases huV with ⟨u', hu', huu'⟩
          have hu_eq : u' = u := Subtype.ext huu'
          rwa [hu_eq] at hu'
      have hn₀_le : (n₀ : ℕ∞) ≤ b := by
        rw [← hW₀_n₀]
        exact hirr W₀ hW₀_irr
      obtain ⟨K, hWK⟩ := exists_isCompl_subrep W₀
      let k' : ℕ := Module.finrank ℂ K.toSubmodule
      have hk_split : n₀ + k' = k := by
        rw [← hW₀_n₀, ← hk]
        exact Submodule.finrank_add_eq_of_isCompl hWK
      have hk'_lt : k' < k := by omega
      obtain ⟨m', n', hn', e', M', hsum', heq'⟩ :=
        ih k' hk'_lt K.toSubmodule rfl K.toRepresentation (irrepDegreesLE_subrep hirr K)
      let B₀ : Module.Basis (Fin n₀) ℂ W₀.toSubmodule :=
        (Module.finBasis ℂ W₀.toSubmodule).reindex (finCongr hW₀_n₀)
      let e₀ : (Fin n₀ → ℂ) ≃ₗ[ℂ] W₀.toSubmodule := B₀.equivFun.symm
      let M₀ : H → Matrix (Fin n₀) (Fin n₀) ℂ := fun x =>
        LinearMap.toMatrix' (e₀.symm.toLinearMap.comp ((W₀.toRepresentation x).comp e₀.toLinearMap))
      have heq₀ : ∀ (x : H) (u₀ : Fin n₀ → ℂ), e₀ ((M₀ x).mulVec u₀) = W₀.toRepresentation x (e₀ u₀) := by
        intro x u₀
        dsimp [M₀]
        rw [LinearMap.toMatrix'_mulVec]
        simp
      let n : Fin (m' + 1) → ℕ := @Fin.cases m' (fun _ => ℕ) n₀ n'
      have hn : ∀ i, (n i : ℕ∞) ≤ b := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact hn₀_le
        · exact hn'
      let e_prod : ((Fin n₀ → ℂ) × State n') ≃ₗ[ℂ] (W₀.toSubmodule × K.toSubmodule) :=
        LinearEquiv.prodCongr e₀ e'
      let e_compl : (W₀.toSubmodule × K.toSubmodule) ≃ₗ[ℂ] V :=
        Submodule.prodEquivOfIsCompl W₀.toSubmodule K.toSubmodule hWK
      let e : State n ≃ₗ[ℂ] V :=
        (stateConsEquiv n₀ n').trans (e_prod.trans e_compl)
      let M : H → ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ := fun x i =>
        @Fin.cases m' (fun i => Matrix (Fin (n i)) (Fin (n i)) ℂ) (M₀ x) (M' x) i
      refine ⟨m' + 1, n, hn, e, M, ?_, ?_⟩
      · simp [n, Fin.sum_univ_succ, hsum', hk_split]
      · intro x u
        let u₀ : Fin n₀ → ℂ := u 0
        let u' : State n' := fun j => u j.succ
        change e_compl (e₀ ((M₀ x).mulVec u₀), e' (fun j => (M' x j).mulVec (u' j))) =
          ρ x (e_compl (e₀ u₀, e' u'))
        rw [heq₀ x u₀, heq' x u']
        change (W₀.toRepresentation x (e₀ u₀)).1 + (K.toRepresentation x (e' u')).1 =
          ρ x ((e₀ u₀).1 + (e' u').1)
        exact (map_add (ρ x) _ _).symm

/-- Upper bound: `trackerDim G b ≤ coverDim G b`. -/
lemma trackerDim_le_coverDim (G : Type u) [Group G] [Finite G] (b : ℕ∞) :
    trackerDim G b ≤ coverDim G b := by
  classical
  unfold coverDim
  refine le_sInf ?_
  rintro D ⟨d, rfl, H, hGrpH, hFinH, φ, ρ, hφ, hρ, hirr⟩
  obtain ⟨m, n, hn, e, M, hsum, heq⟩ :=
    exists_block_diag b d (Fin d → ℂ) (Module.finrank_fin_fun ℂ) ρ hirr
  obtain ⟨v₀, hv₀⟩ := exists_injective_orbit ρ hρ
  choose σ hσ using hφ
  let T : Tracker G b :=
    { m := m
      n := n
      n_le := hn
      A := fun g i => M (σ g) i
      c := fun _ => 0
      h₀ := e.symm v₀
      dec := fun u => if h : ∃ x : H, e.symm (ρ x v₀) = u then φ (Classical.choose h) else 1 }
  let liftWord : List G → H := fun s => (s.map σ).reverse.prod
  have hword : ∀ s : List G, T.wordMap s T.h₀ = e.symm (ρ (liftWord s) v₀) ∧
      φ (liftWord s) = wordProd s := by
    intro s
    induction s using List.reverseRecOn with
    | nil =>
      simp [T, liftWord]
    | append_singleton s g ih =>
      rcases ih with ⟨ih₁, ih₂⟩
      constructor
      · rw [wordMap_append, wordMap_singleton, ih₁]
        have hstep : T.step g (e.symm (ρ (liftWord s) v₀)) =
            fun i => (M (σ g) i).mulVec ((e.symm (ρ (liftWord s) v₀)) i) := by
          funext i
          simp [Tracker.step, T]
        rw [hstep]
        apply e.injective
        rw [heq (σ g) (e.symm (ρ (liftWord s) v₀))]
        simp [liftWord, List.reverse_append, map_mul]
      · simp [liftWord, List.reverse_append, map_mul, hσ, ih₂, wordProd]
  have hTracks : T.Tracks := by
    intro s
    rcases hword s with ⟨hs₁, hs₂⟩
    dsimp [T]
    rw [hs₁]
    have hex : ∃ x : H, e.symm (ρ x v₀) = e.symm (ρ (liftWord s) v₀) := ⟨liftWord s, rfl⟩
    rw [dif_pos hex]
    have hchoose_eq : Classical.choose hex = liftWord s :=
      hv₀ (e.symm.injective (Classical.choose_spec hex))
    rw [hchoose_eq, hs₂]
  have hFinState : T.IsFiniteState := by
    refine Set.Finite.subset (Set.finite_range (fun x : H => e.symm (ρ x v₀))) ?_
    rintro u ⟨s, rfl⟩
    exact ⟨liftWord s, (hword s).1.symm⟩
  have hdim : T.hiddenDim = d := hsum
  unfold trackerDim
  exact sInf_le ⟨T, hTracks, hFinState, by rw [hdim]⟩

end UpperBound

/-! ### Part 3: Direction 2 (`coverDim G b ≤ trackerDim G b`) -/

section LowerBound

/-- Block-diagonal affine endomorphisms `(L_i, v_i)_{i : Fin m}` on a product of `ℂ`-modules. -/
structure BlockAff {m : ℕ} (U : Fin m → Type*) [∀ i, AddCommGroup (U i)] [∀ i, Module ℂ (U i)] where
  L : ∀ i, U i →ₗ[ℂ] U i
  v : ∀ i, U i

namespace BlockAff

variable {m : ℕ} {U : Fin m → Type*} [∀ i, AddCommGroup (U i)] [∀ i, Module ℂ (U i)]

/-- Evaluate block `i` of a `BlockAff` at `u : U i`. -/
def eval (f : BlockAff U) (i : Fin m) (u : U i) : U i :=
  f.L i u + f.v i

lemma ext_eval {f₁ f₂ : BlockAff U} (h : ∀ i u, f₁.eval i u = f₂.eval i u) : f₁ = f₂ := by
  have hv : f₁.v = f₂.v := by
    funext i
    simpa [eval] using h i 0
  have hL : f₁.L = f₂.L := by
    funext i
    refine LinearMap.ext fun u => ?_
    have hi := h i u
    dsimp [eval] at hi
    rw [hv] at hi
    exact add_right_cancel hi
  cases f₁; cases f₂
  cases hv; cases hL
  rfl

instance : One (BlockAff U) where
  one := { L := fun _ => LinearMap.id, v := fun _ => 0 }

instance : Mul (BlockAff U) where
  mul f₁ f₂ :=
    { L := fun i => (f₁.L i).comp (f₂.L i)
      v := fun i => f₁.L i (f₂.v i) + f₁.v i }

@[simp]
lemma one_L (i : Fin m) : (1 : BlockAff U).L i = LinearMap.id := rfl

@[simp]
lemma one_v (i : Fin m) : (1 : BlockAff U).v i = 0 := rfl

@[simp]
lemma mul_L (f₁ f₂ : BlockAff U) (i : Fin m) : (f₁ * f₂).L i = (f₁.L i).comp (f₂.L i) := rfl

@[simp]
lemma mul_v (f₁ f₂ : BlockAff U) (i : Fin m) : (f₁ * f₂).v i = f₁.L i (f₂.v i) + f₁.v i := rfl

instance : Monoid (BlockAff U) where
  one_mul f := by
    apply ext_eval
    intro i u
    simp [eval]
  mul_one f := by
    apply ext_eval
    intro i u
    simp [eval]
  mul_assoc f₁ f₂ f₃ := by
    apply ext_eval
    intro i u
    simp [eval, add_assoc]

@[simp]
lemma one_eval (i : Fin m) (u : U i) : (1 : BlockAff U).eval i u = u := by
  simp [eval]

@[simp]
lemma mul_eval (f₁ f₂ : BlockAff U) (i : Fin m) (u : U i) :
    (f₁ * f₂).eval i u = f₁.eval i (f₂.eval i u) := by
  simp [eval, add_assoc]

end BlockAff

/-- Every finite monoid `M` contains a minimal-left-ideal idempotent `e` such that
`{ x : M // e * x * e = x }` forms a finite group under multiplication of `M` with identity `e`. -/
lemma exists_minimal_idempotent_group (M : Type) [Monoid M] [Finite M] :
    ∃ e : M, e * e = e ∧
      ∀ x : M, e * x * e = x → ∃ y : M, e * y * e = y ∧ y * x = e := by
  classical
  haveI : Fintype M := Fintype.ofFinite M
  let leftIdeal : M → Finset M := fun m => Finset.univ.image (fun u => u * m)
  obtain ⟨m₀, _, hm₀_min⟩ :=
    Finset.exists_min_image Finset.univ (fun m => (leftIdeal m).card) ⟨1, Finset.mem_univ 1⟩
  let L : Finset M := leftIdeal m₀
  have hL_eq : ∀ y ∈ L, leftIdeal y = L := by
    intro y hy
    have hsub : leftIdeal y ⊆ L := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨u, _, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨v, _, rfl⟩
      exact Finset.mem_image.mpr ⟨u * v, Finset.mem_univ _, mul_assoc u v m₀⟩
    exact Finset.eq_of_subset_of_card_le hsub (hm₀_min y (Finset.mem_univ y))
  have hpow_mem : ∀ n : ℕ, m₀ ^ (n + 1) ∈ L := by
    intro n
    induction n with
    | zero =>
      rw [zero_add, pow_one]
      exact Finset.mem_image.mpr ⟨1, Finset.mem_univ 1, one_mul m₀⟩
    | succ n ih =>
      rw [← hL_eq (m₀ ^ (n + 1)) ih]
      exact Finset.mem_image.mpr ⟨m₀, Finset.mem_univ m₀, (pow_succ' m₀ (n + 1)).symm⟩
  obtain ⟨a, b, hab_ne, hab_eq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => m₀ ^ (n + 1))
  change m₀ ^ (a + 1) = m₀ ^ (b + 1) at hab_eq
  have hex_period : ∃ i d : ℕ, 0 < d ∧ m₀ ^ (i + 1) = m₀ ^ (i + 1) * m₀ ^ d := by
    rcases lt_trichotomy a b with hab | rfl | hba
    · refine ⟨a, b - a, Nat.sub_pos_of_lt hab, ?_⟩
      have hba_eq : b + 1 = (a + 1) + (b - a) := by omega
      calc
        m₀ ^ (a + 1) = m₀ ^ (b + 1) := hab_eq
        _ = m₀ ^ ((a + 1) + (b - a)) := by rw [hba_eq]
        _ = m₀ ^ (a + 1) * m₀ ^ (b - a) := pow_add _ _ _
    · exact (hab_ne rfl).elim
    · refine ⟨b, a - b, Nat.sub_pos_of_lt hba, ?_⟩
      have hab_eq' : a + 1 = (b + 1) + (a - b) := by omega
      calc
        m₀ ^ (b + 1) = m₀ ^ (a + 1) := hab_eq.symm
        _ = m₀ ^ ((b + 1) + (a - b)) := by rw [hab_eq']
        _ = m₀ ^ (b + 1) * m₀ ^ (a - b) := pow_add _ _ _
  obtain ⟨i, d, hd_pos, hper⟩ := hex_period
  have hper_iter : ∀ k : ℕ, m₀ ^ (i + 1) * (m₀ ^ d) ^ k = m₀ ^ (i + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ (m₀ ^ d) k, ← mul_assoc, ih, ← hper]
  let N : ℕ := d * (i + 1)
  have hN_ge : i + 1 ≤ N := by
    calc
      i + 1 = 1 * (i + 1) := (one_mul _).symm
      _ ≤ d * (i + 1) := Nat.mul_le_mul_right (i + 1) hd_pos
  have hN_pos : 0 < N := lt_of_lt_of_le (Nat.succ_pos i) hN_ge
  let e : M := m₀ ^ N
  have he_mem : e ∈ L := by
    have : N = (N - 1) + 1 := by omega
    dsimp [e]
    rw [this]
    exact hpow_mem (N - 1)
  have he_idem : e * e = e := by
    dsimp [e]
    have hsplit : N = (N - (i + 1)) + (i + 1) := by omega
    calc
      m₀ ^ N * m₀ ^ N
          = m₀ ^ ((N - (i + 1)) + (i + 1)) * (m₀ ^ d) ^ (i + 1) := by
              rw [← hsplit, ← pow_mul]
      _ = m₀ ^ (N - (i + 1)) * (m₀ ^ (i + 1) * (m₀ ^ d) ^ (i + 1)) := by
              rw [pow_add, mul_assoc]
      _ = m₀ ^ (N - (i + 1)) * m₀ ^ (i + 1) := by
              rw [hper_iter (i + 1)]
      _ = m₀ ^ N := by
              rw [← pow_add, ← hsplit]
  refine ⟨e, he_idem, ?_⟩
  intro x hx
  have hx_mem : x ∈ L := by
    rw [← hx, ← hL_eq e he_mem]
    exact Finset.mem_image.mpr ⟨e * x, Finset.mem_univ _, rfl⟩
  have hLx : leftIdeal x = L := hL_eq x hx_mem
  have he_in_Lx : e ∈ leftIdeal x := by rwa [hLx]
  rcases Finset.mem_image.mp he_in_Lx with ⟨u, _, hux⟩
  refine ⟨e * u * e, ?_, ?_⟩
  · calc
      e * (e * u * e) * e = (e * e) * u * (e * e) := by simp [mul_assoc]
      _ = e * u * e := by rw [he_idem]
  · have hex : e * x = x := by
      calc
        e * x = e * (e * x * e) := by rw [hx]
        _ = (e * e) * x * e := by simp [mul_assoc]
        _ = x := by rw [he_idem, hx]
    calc
      (e * u * e) * x = e * u * (e * x) := by simp [mul_assoc]
      _ = e * (u * x) := by rw [hex, mul_assoc]
      _ = e * e := by rw [hux]
      _ = e := he_idem

/-- Turn `{ x : M // e * x * e = x }` with left inverses into a `Group`. -/
def CornerSubtype (M : Type) [Monoid M] (e : M) : Type :=
  { x : M // e * x * e = x }

section CornerGroup

variable {M : Type} [Monoid M] {e : M}

lemma corner_left_id (he : e * e = e) (x : CornerSubtype M e) : e * x.1 = x.1 := by
  calc
    e * x.1 = e * (e * x.1 * e) := by rw [x.2]
    _ = (e * e) * x.1 * e := by simp [mul_assoc]
    _ = x.1 := by rw [he, x.2]

lemma corner_right_id (he : e * e = e) (x : CornerSubtype M e) : x.1 * e = x.1 := by
  calc
    x.1 * e = (e * x.1 * e) * e := by rw [x.2]
    _ = e * x.1 * (e * e) := by simp [mul_assoc]
    _ = x.1 := by rw [he, x.2]

/-- From any finite monoid `M` surjecting onto a group `G`, extract a finite group `H : Type`
surjecting onto `G` together with an injective multiplicative map `ι : H → M`. -/
lemma exists_group_cover_of_finite_monoid {G : Type u} [Group G]
    (M : Type) [Monoid M] [Finite M] (π_M : M →* G) (hπ_surj : Function.Surjective π_M) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H) (φ : H →* G) (ι : H → M),
      Function.Surjective φ ∧ Function.Injective ι ∧ ∀ x y : H, ι (x * y) = ι x * ι y := by
  obtain ⟨e, he_idem, he_inv⟩ := exists_minimal_idempotent_group M
  let H : Type := CornerSubtype M e
  let mulH : H → H → H := fun x y =>
    ⟨x.1 * y.1, by
      calc
        e * (x.1 * y.1) * e = (e * x.1) * (y.1 * e) := by simp [mul_assoc]
        _ = x.1 * y.1 := by rw [corner_left_id he_idem x, corner_right_id he_idem y]⟩
  let oneH : H := ⟨e, by rw [he_idem, he_idem]⟩
  have hleft_inv : ∀ x : H, ∃ y : H, mulH y x = oneH := by
    intro x
    obtain ⟨y, hy, hyx⟩ := he_inv x.1 x.2
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  choose invH hinvH using hleft_inv
  let grpH : Group H :=
    { mul := mulH
      one := oneH
      inv := invH
      mul_assoc := fun a b c => Subtype.ext (mul_assoc a.1 b.1 c.1)
      one_mul := fun a => Subtype.ext (corner_left_id he_idem a)
      mul_one := fun a => Subtype.ext (corner_right_id he_idem a)
      inv_mul_cancel := hinvH }
  letI : Group H := grpH
  have hFinH : Finite H := by dsimp [H, CornerSubtype]; infer_instance
  have hπ_e : π_M e = 1 := by
    have hmul_e : π_M e * π_M e = π_M e * 1 := by
      rw [← map_mul, he_idem, mul_one]
    exact mul_left_cancel hmul_e
  let φ : H →* G :=
    { toFun := fun h => π_M h.1
      map_one' := hπ_e
      map_mul' := fun h₁ h₂ => map_mul π_M h₁.1 h₂.1 }
  have hφ_surj : Function.Surjective φ := by
    intro g
    obtain ⟨m, rfl⟩ := hπ_surj g
    let h : H := ⟨e * m * e, by
      calc
        e * (e * m * e) * e = (e * e) * m * (e * e) := by simp [mul_assoc]
        _ = e * m * e := by rw [he_idem]⟩
    refine ⟨h, ?_⟩
    change π_M (e * m * e) = π_M m
    simp [map_mul, hπ_e]
  exact ⟨H, grpH, hFinH, φ, Subtype.val, hφ_surj, Subtype.val_injective, fun _ _ => rfl⟩

end CornerGroup

/-- Product of `m` complex representations `ρ_i` on `∀ i : Fin m, W i`. -/
def piRep {H : Type*} [Group H] {m : ℕ}
    (W : Fin m → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ_i : ∀ i, Representation ℂ H (W i)) :
    Representation ℂ H (∀ i, W i) where
  toFun h :=
    { toFun := fun w i => ρ_i i h (w i)
      map_add' := fun w₁ w₂ => by funext i; exact map_add (ρ_i i h) (w₁ i) (w₂ i)
      map_smul' := fun c w => by funext i; exact map_smul (ρ_i i h) c (w i) }
  map_one' := by
    refine LinearMap.ext fun w => funext fun i => ?_
    simp
  map_mul' h₁ h₂ := by
    refine LinearMap.ext fun w => funext fun i => ?_
    simp

/-- Every irreducible subrepresentation of `piRep W ρ_i` embeds into one factor `W i`, so its
dimension is bounded by `b` whenever each `W i` has `finrank ≤ b`. -/
lemma irrepDegreesLE_piRep {H : Type*} [Group H] {m : ℕ}
    (W : Fin m → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [∀ i, FiniteDimensional ℂ (W i)]
    (ρ_i : ∀ i, Representation ℂ H (W i)) {b : ℕ∞}
    (hW_le : ∀ i, (Module.finrank ℂ (W i) : ℕ∞) ≤ b) :
    IrrepDegreesLE (piRep W ρ_i) b := by
  intro Z hZ
  have : IsSimpleOrder (Subrepresentation Z.toRepresentation) := hZ
  have hbt : (⊥ : Subrepresentation Z.toRepresentation) ≠ ⊤ := bot_ne_top
  have hex_z : ∃ z : Z.toSubmodule, z ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hbt
    apply subrep_ext
    change (⊥ : Submodule ℂ Z.toSubmodule) = ⊤
    ext z
    simp [hall z]
  rcases hex_z with ⟨z, hz_ne⟩
  have hz1_ne : z.1 ≠ 0 := fun h0 => hz_ne (Subtype.ext h0)
  obtain ⟨i, hi_ne⟩ := Function.ne_iff.mp hz1_ne
  let π_i : Z.toSubmodule →ₗ[ℂ] W i := (LinearMap.proj i).comp Z.toSubmodule.subtype
  let K_i : Subrepresentation Z.toRepresentation :=
    { toSubmodule := LinearMap.ker π_i
      apply_mem_toSubmodule := by
        intro h u hu
        have hu0 : u.1 i = 0 := hu
        change ρ_i i h (u.1 i) = 0
        rw [hu0, map_zero] }
  rcases eq_bot_or_eq_top K_i with hK_bot | hK_top
  · have hker_bot : LinearMap.ker π_i = ⊥ := congrArg Subrepresentation.toSubmodule hK_bot
    have hπ_inj : Function.Injective π_i := LinearMap.ker_eq_bot.mp hker_bot
    have hle₁ : Module.finrank ℂ Z.toSubmodule ≤ Module.finrank ℂ (W i) :=
      LinearMap.finrank_le_finrank_of_injective hπ_inj
    exact le_trans (Nat.cast_le.mpr hle₁) (hW_le i)
  · exfalso
    have hz_mem : z ∈ K_i.toSubmodule := by rw [hK_top]; trivial
    exact hi_ne hz_mem

/-- Given a finite group `H` surjecting onto `G` with an injective multiplicative block-affine
action on subspaces `U i ≤ (Fin (n i) → ℂ)` with `(n i : ℕ∞) ≤ b`, deduce
`coverDim G b ≤ ((∑ i, n i : ℕ) : ℕ∞)`. -/
lemma coverDim_le_of_corner {G : Type u} [Group G] {b : ℕ∞}
    {m : ℕ} {n : Fin m → ℕ} (hn_le : ∀ i, (n i : ℕ∞) ≤ b)
    (U : ∀ i : Fin m, Submodule ℂ (Fin (n i) → ℂ))
    (H : Type) [Group H] [Finite H]
    (φ : H →* G) (hφ_surj : Function.Surjective φ)
    (aff : H → BlockAff (fun i => U i))
    (haff_inj : Function.Injective aff)
    (haff_mul : ∀ h₁ h₂ : H, aff (h₁ * h₂) = aff h₁ * aff h₂) :
    coverDim G b ≤ ((∑ i, n i : ℕ) : ℕ∞) := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  let p : ∀ i : Fin m, U i := fun i =>
    (Fintype.card H : ℂ)⁻¹ • ∑ x : H, (aff x).v i
  have hp_fixed : ∀ (h : H) (i : Fin m), (aff h).eval i (p i) = p i := by
    intro h i
    have hcard_ne : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hv_avg : (aff h).v i = (Fintype.card H : ℂ)⁻¹ • ∑ _x : H, (aff h).v i := by
      rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hcard_ne]
    have hsum_eq : ∑ x : H, ((aff h).L i ((aff x).v i) + (aff h).v i) = ∑ x : H, (aff x).v i := by
      have hterm : ∀ x : H, (aff h).L i ((aff x).v i) + (aff h).v i = (aff (h * x)).v i := by
        intro x
        rw [haff_mul h x, BlockAff.mul_v]
      simp_rw [hterm]
      exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)
    calc
      (aff h).eval i (p i)
          = (aff h).L i ((Fintype.card H : ℂ)⁻¹ • ∑ x : H, (aff x).v i) + (aff h).v i := rfl
      _ = (Fintype.card H : ℂ)⁻¹ • (∑ x : H, (aff h).L i ((aff x).v i)) +
            (Fintype.card H : ℂ)⁻¹ • (∑ _x : H, (aff h).v i) := by
            rw [map_smul, map_sum, ← hv_avg]
      _ = (Fintype.card H : ℂ)⁻¹ • ∑ x : H, ((aff h).L i ((aff x).v i) + (aff h).v i) := by
            rw [← smul_add, ← Finset.sum_add_distrib]
      _ = p i := by rw [hsum_eq]
  have heval_lin : ∀ (h : H) (i : Fin m) (u : U i),
      (aff h).eval i u = p i + (aff h).L i (u - p i) := by
    intro h i u
    have hpf := hp_fixed h i
    dsimp [BlockAff.eval] at hpf ⊢
    calc
      (aff h).L i u + (aff h).v i
          = ((aff h).L i (p i) + (aff h).v i) + ((aff h).L i u - (aff h).L i (p i)) := by abel
      _ = p i + (aff h).L i (u - p i) := by rw [hpf, map_sub]
  let W : ∀ i : Fin m, Submodule ℂ (U i) := fun i => LinearMap.range ((aff 1).L i)
  have he_L_idem : ∀ (i : Fin m) (w : W i), (aff 1).L i w.1 = w.1 := by
    intro i w
    rcases w.2 with ⟨u, hu⟩
    rw [← hu]
    have hidem : (aff 1 * aff 1).L i = (aff 1).L i := by
      rw [← haff_mul 1 1, mul_one]
    exact LinearMap.congr_fun hidem u
  have hh_L_mem : ∀ (h : H) (i : Fin m) (u : U i), (aff h).L i u ∈ W i := by
    intro h i u
    have heh : (aff 1 * aff h).L i = (aff h).L i := by
      rw [← haff_mul 1 h, one_mul]
    rw [← heh]
    exact ⟨(aff h).L i u, rfl⟩
  let ρ_i : ∀ i : Fin m, Representation ℂ H (W i) := fun i =>
    { toFun := fun h =>
        { toFun := fun w => ⟨(aff h).L i w.1, hh_L_mem h i w.1⟩
          map_add' := fun w₁ w₂ => Subtype.ext (map_add ((aff h).L i) w₁.1 w₂.1)
          map_smul' := fun c w => Subtype.ext (map_smul ((aff h).L i) c w.1) }
      map_one' := by
        refine LinearMap.ext fun w => Subtype.ext (he_L_idem i w)
      map_mul' := fun h₁ h₂ => by
        refine LinearMap.ext fun w => Subtype.ext ?_
        have hm : (aff (h₁ * h₂)).L i = ((aff h₁).L i).comp ((aff h₂).L i) := by
          rw [haff_mul h₁ h₂, BlockAff.mul_L]
        exact LinearMap.congr_fun hm w.1 }
  let ρ_prod := piRep (fun i => W i) ρ_i
  have hW_dim : ∀ i : Fin m, Module.finrank ℂ (W i) ≤ n i := by
    intro i
    calc
      Module.finrank ℂ (W i) ≤ Module.finrank ℂ (U i) := Submodule.finrank_le (W i)
      _ ≤ Module.finrank ℂ (Fin (n i) → ℂ) := Submodule.finrank_le (U i)
      _ = n i := Module.finrank_fin_fun ℂ
  have hρ_prod_inj : Function.Injective ρ_prod := by
    intro h₁ h₂ h12
    apply haff_inj
    apply BlockAff.ext_eval
    intro i u
    rw [heval_lin h₁ i u, heval_lin h₂ i u]
    congr 1
    have hL_eq : ∀ z : U i, (aff h₁).L i z = (aff h₂).L i z := by
      intro z
      let wz : W i := ⟨(aff 1).L i z, z, rfl⟩
      let w : ∀ j : Fin m, W j := Pi.single i wz
      have hw := congrArg (fun f : (∀ j : Fin m, W j) →ₗ[ℂ] (∀ j : Fin m, W j) => (f w i).1) h12
      dsimp [ρ_prod, piRep, ρ_i, w, wz] at hw
      simp only [Pi.single_eq_same] at hw
      have hr₁ : ((aff h₁).L i).comp ((aff 1).L i) = (aff h₁).L i := by
        change (aff h₁ * aff 1).L i = (aff h₁).L i
        rw [← haff_mul h₁ 1, mul_one]
      have hr₂ : ((aff h₂).L i).comp ((aff 1).L i) = (aff h₂).L i := by
        change (aff h₂ * aff 1).L i = (aff h₂).L i
        rw [← haff_mul h₂ 1, mul_one]
      have h1z := LinearMap.congr_fun hr₁ z
      have h2z := LinearMap.congr_fun hr₂ z
      dsimp at h1z h2z
      rw [← h1z, ← h2z]
      exact hw
    exact hL_eq (u - p i)
  have hirr_prod :=
    irrepDegreesLE_piRep (fun i => W i) ρ_i
      (fun i => le_trans (Nat.cast_le.mpr (hW_dim i)) (hn_le i))
  have : ∀ i : Fin m, Module.Free ℂ (W i) := fun i => Module.Free.of_divisionRing ℂ (W i)
  have : Module.Free ℂ (∀ i : Fin m, W i) := Module.Free.of_divisionRing ℂ (∀ i : Fin m, W i)
  let d : ℕ := Module.finrank ℂ (∀ i : Fin m, W i)
  have hd_le : d ≤ ∑ i, n i := by
    dsimp [d]
    rw [Module.finrank_pi_fintype ℂ]
    exact Finset.sum_le_sum (fun i _ => hW_dim i)
  let e_fin : (∀ i : Fin m, W i) ≃ₗ[ℂ] (Fin d → ℂ) :=
    (Module.finBasis ℂ (∀ i : Fin m, W i)).equivFun
  let ρ : Representation ℂ H (Fin d → ℂ) :=
    { toFun := fun h => e_fin.toLinearMap.comp ((ρ_prod h).comp e_fin.symm.toLinearMap)
      map_one' := by
        refine LinearMap.ext fun v => ?_
        simp
      map_mul' := fun h₁ h₂ => by
        refine LinearMap.ext fun v => ?_
        simp }
  have he_fin_equiv : ∀ (h : H) (v : ∀ i : Fin m, W i), e_fin (ρ_prod h v) = ρ h (e_fin v) := by
    intro h v
    simp [ρ]
  have hρ_inj : Function.Injective ρ := by
    intro h₁ h₂ h12
    apply hρ_prod_inj
    refine LinearMap.ext fun v => ?_
    apply e_fin.injective
    rw [he_fin_equiv, he_fin_equiv, h12]
  have hirr_ρ : IrrepDegreesLE ρ b :=
    irrepDegreesLE_of_equiv e_fin he_fin_equiv hirr_prod
  have hcover_le_d : coverDim G b ≤ (d : ℕ∞) := by
    unfold coverDim
    exact sInf_le ⟨d, rfl, H, inferInstance, inferInstance, φ, ρ, hφ_surj, hρ_inj, hirr_ρ⟩
  exact le_trans hcover_le_d (Nat.cast_le.mpr hd_le)

/-- Lower bound: `coverDim G b ≤ trackerDim G b`. -/
lemma coverDim_le_trackerDim (G : Type u) [Group G] [Finite G] (b : ℕ∞) :
    coverDim G b ≤ trackerDim G b := by
  classical
  unfold trackerDim
  refine le_sInf ?_
  rintro D ⟨T, hTracks, hFin, rfl⟩
  -- 1. Shifted reachable sets and their `ℂ`-linear spans `U i`.
  let S : ∀ i : Fin T.m, Set (Fin (T.n i) → ℂ) :=
    fun i => (fun r : State T.n => r i - T.h₀ i) '' T.reach
  have hS_fin : ∀ i, (S i).Finite := fun i => hFin.image _
  have h0_mem_S : ∀ i, (0 : Fin (T.n i) → ℂ) ∈ S i := by
    intro i
    exact ⟨T.h₀, ⟨[], rfl⟩, sub_self (T.h₀ i)⟩
  let U : ∀ i : Fin T.m, Submodule ℂ (Fin (T.n i) → ℂ) :=
    fun i => Submodule.span ℂ (S i)
  have hU_inv : ∀ (i : Fin T.m) (s : List G) (u : Fin (T.n i) → ℂ),
      u ∈ U i → (blockMat T i s).mulVec u ∈ U i := by
    intro i s
    have hle : U i ≤ (U i).comap (Matrix.mulVecLin (blockMat T i s)) := by
      refine Submodule.span_le.mpr ?_
      rintro y ⟨r, ⟨t, rfl⟩, rfl⟩
      change (blockMat T i s).mulVec (T.wordMap t T.h₀ i - T.h₀ i) ∈ U i
      rw [← blockWordMap_sub T i s, ← wordMap_apply, ← wordMap_apply, ← wordMap_append]
      have h₁ : T.wordMap (t ++ s) T.h₀ i - T.h₀ i ∈ U i :=
        Submodule.subset_span ⟨T.wordMap (t ++ s) T.h₀, ⟨t ++ s, rfl⟩, rfl⟩
      have h₂ : T.wordMap s T.h₀ i - T.h₀ i ∈ U i :=
        Submodule.subset_span ⟨T.wordMap s T.h₀, ⟨s, rfl⟩, rfl⟩
      have hsub := Submodule.sub_mem (U i) h₁ h₂
      simpa [sub_sub_sub_cancel_right] using hsub
    intro u hu
    exact hle hu
  -- 2. Block-affine word action on `U`.
  let wordAff : List G → BlockAff (fun i => U i) := fun s =>
    { L := fun i =>
        { toFun := fun u => ⟨(blockMat T i s).mulVec u.1, hU_inv i s u.1 u.2⟩
          map_add' := fun u₁ u₂ => Subtype.ext (Matrix.mulVec_add _ u₁.1 u₂.1)
          map_smul' := fun c u => Subtype.ext (Matrix.mulVec_smul _ c u.1) }
      v := fun i =>
        ⟨T.wordMap s T.h₀ i - T.h₀ i,
          Submodule.subset_span ⟨T.wordMap s T.h₀, ⟨s, rfl⟩, rfl⟩⟩ }
  have hwordAff_eval : ∀ (s : List G) (i : Fin T.m) (u : U i),
      ((wordAff s).eval i u).1 = blockWordMap T i s (T.h₀ i + u.1) - T.h₀ i := by
    intro s i u
    dsimp [BlockAff.eval, wordAff]
    have hdiff := blockWordMap_sub T i s (T.h₀ i + u.1) (T.h₀ i)
    rw [add_sub_cancel_left] at hdiff
    rw [← hdiff, wordMap_apply]
    abel
  have hwordAff_nil : wordAff [] = 1 := by
    apply BlockAff.ext_eval
    intro i u
    apply Subtype.ext
    rw [hwordAff_eval]
    simp [blockWordMap]
  have hwordAff_append : ∀ s₁ s₂ : List G, wordAff (s₁ ++ s₂) = wordAff s₂ * wordAff s₁ := by
    intro s₁ s₂
    apply BlockAff.ext_eval
    intro i u
    apply Subtype.ext
    rw [BlockAff.mul_eval, hwordAff_eval, hwordAff_eval, hwordAff_eval, blockWordMap_append]
    have heq : T.h₀ i + (blockWordMap T i s₁ (T.h₀ i + u.1) - T.h₀ i) =
        blockWordMap T i s₁ (T.h₀ i + u.1) := add_sub_cancel _ _
    rw [heq]
  -- 3. Finite transition submonoid `M : Type` and surjective monoid hom `π_M : M →* G`.
  let M_sub : Submonoid (BlockAff (fun i => U i)) :=
    { carrier := Set.range wordAff
      one_mem' := ⟨[], hwordAff_nil⟩
      mul_mem' := by
        rintro _ _ ⟨s₂, rfl⟩ ⟨s₁, rfl⟩
        exact ⟨s₁ ++ s₂, hwordAff_append s₁ s₂⟩ }
  let S' : ∀ i : Fin T.m, Set (U i) := fun i => { u : U i | u.1 ∈ S i }
  have hS'_fin : ∀ i, (S' i).Finite := by
    intro i
    exact (hS_fin i).preimage Subtype.val_injective.injOn
  have hS'_span : ∀ i, Submodule.span ℂ (S' i) = ⊤ := by
    intro i
    rw [eq_top_iff]
    intro u _
    have hu : u.1 ∈ Submodule.span ℂ (S i) := u.2
    have himg : (U i).subtype '' S' i = S i := by
      ext x
      simp only [Set.mem_image, S']
      constructor
      · rintro ⟨w, hw, rfl⟩; exact hw
      · intro hx; exact ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩
    rw [← himg, ← Submodule.map_span] at hu
    rcases hu with ⟨w, hw, hwu⟩
    have : w = u := (U i).injective_subtype hwu
    simpa [this] using hw
  have hS'_maps : ∀ (s : List G) (i : Fin T.m) (u : S' i),
      (wordAff s).eval i u.1 ∈ S' i := by
    intro s i u
    rcases u.2 with ⟨r, ⟨t, rfl⟩, hr⟩
    dsimp at hr
    change ((wordAff s).eval i u.1).1 ∈ S i
    rw [hwordAff_eval]
    have hru : T.h₀ i + u.1.1 = T.wordMap t T.h₀ i := by
      rw [← hr]
      abel
    rw [hru, ← wordMap_apply, ← wordMap_append]
    exact ⟨T.wordMap (t ++ s) T.h₀, ⟨t ++ s, rfl⟩, rfl⟩
  have : ∀ i, Finite (S' i) := fun i => (hS'_fin i).to_subtype
  let res : M_sub → ∀ i : Fin T.m, S' i → S' i := fun m_elem i u =>
    ⟨m_elem.1.eval i u.1, by
      rcases m_elem.2 with ⟨s, hs⟩
      rw [← hs]
      exact hS'_maps s i u⟩
  have hres_inj : Function.Injective res := by
    intro f₁ f₂ hres
    apply Subtype.ext
    have hv_eq : ∀ i, f₁.1.v i = f₂.1.v i := by
      intro i
      let u0 : S' i := ⟨0, h0_mem_S i⟩
      have h0 := congrArg (fun g => (g i u0).1) hres
      simpa [res, u0, BlockAff.eval] using h0
    have hL_eq : ∀ i, f₁.1.L i = f₂.1.L i := by
      intro i
      have htop : LinearMap.eqLocus (f₁.1.L i) (f₂.1.L i) = ⊤ := by
        rw [← top_le_iff, ← hS'_span i, Submodule.span_le]
        intro u hu
        change f₁.1.L i u = f₂.1.L i u
        have hu_eq := congrArg (fun g => (g i ⟨u, hu⟩).1) hres
        dsimp [res, BlockAff.eval] at hu_eq
        rw [hv_eq i] at hu_eq
        exact add_right_cancel hu_eq
      refine LinearMap.ext fun u => ?_
      have hu_mem : u ∈ LinearMap.eqLocus (f₁.1.L i) (f₂.1.L i) := by
        rw [htop]; trivial
      exact hu_mem
    apply BlockAff.ext_eval
    intro i u
    simp [BlockAff.eval, hv_eq i, hL_eq i]
  have : Finite M_sub := Finite.of_injective res hres_inj
  have hwordAff_prod : ∀ s₁ s₂ : List G, wordAff s₁ = wordAff s₂ → wordProd s₁ = wordProd s₂ := by
    intro s₁ s₂ hs
    have hmap : T.wordMap s₁ T.h₀ = T.wordMap s₂ T.h₀ := by
      funext i
      have hvi : ((wordAff s₁).v i).1 = ((wordAff s₂).v i).1 := by rw [hs]
      dsimp [wordAff] at hvi
      exact sub_left_injective hvi
    rw [← hTracks s₁, ← hTracks s₂, hmap]
  have hπ_spec : ∀ (x : M_sub) (s : List G), wordAff s = x.1 →
      wordProd (Classical.choose x.2) = wordProd s := by
    intro x s hs
    exact hwordAff_prod _ _ ((Classical.choose_spec x.2).trans hs.symm)
  let π_M : M_sub →* G :=
    { toFun := fun x => wordProd (Classical.choose x.2)
      map_one' := by
        rw [hπ_spec 1 [] hwordAff_nil, wordProd_nil]
      map_mul' := by
        intro x y
        let s₁ := Classical.choose x.2
        let s₂ := Classical.choose y.2
        have hs₁ : wordAff s₁ = x.1 := Classical.choose_spec x.2
        have hs₂ : wordAff s₂ = y.1 := Classical.choose_spec y.2
        have hmul : wordAff (s₂ ++ s₁) = (x * y).1 := by
          change wordAff (s₂ ++ s₁) = x.1 * y.1
          rw [hwordAff_append, hs₁, hs₂]
        rw [hπ_spec (x * y) (s₂ ++ s₁) hmul, wordProd_append] }
  have hπ_surj : Function.Surjective π_M := by
    intro g
    refine ⟨⟨wordAff [g], [g], rfl⟩, ?_⟩
    dsimp [π_M]
    rw [hπ_spec ⟨wordAff [g], [g], rfl⟩ [g] rfl, wordProd_singleton]
  -- 4. Extract corner group cover `H : Type` and apply `coverDim_le_of_corner`.
  obtain ⟨H, hGrpH, hFinH, φ, ι, hφ_surj, hι_inj, hι_mul⟩ :=
    exists_group_cover_of_finite_monoid M_sub π_M hπ_surj
  exact @coverDim_le_of_corner G _ b T.m T.n T.n_le U H hGrpH hFinH φ hφ_surj
    (fun h => (ι h).1)
    (fun h₁ h₂ h12 => hι_inj (Subtype.ext h12))
    (fun h₁ h₂ => congrArg Subtype.val (hι_mul h₁ h₂))

end LowerBound

theorem theorem_4_proof (G : Type u) [Group G] [Finite G] (b : ℕ∞) (_hb : 1 ≤ b) :
    trackerDim G b = coverDim G b :=
  le_antisymm (trackerDim_le_coverDim G b) (coverDim_le_trackerDim G b)

end BlockSSM_Proof

open BlockSSM

theorem solution (G : Type u) [Group G] [Finite G] (b : ℕ∞) (hb : 1 ≤ b) :
    trackerDim G b = coverDim G b :=
  BlockSSM_Proof.theorem_4_proof G b hb

