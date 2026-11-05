-- Prove2me | solution 1 for CostSharingPNE.Char.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:44:07.976398+00:00
-- url     : https://prove2.me/submissions/4a0b08a9-5633-4051-a1b7-b380f102550e

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Definitions.Def_CostSharingPNE_Char_Basis
import Theorems.Thm_CostSharingPNE_Char_lemma_5

open CostSharingPNE.Char

namespace CSPLemma7Aux

variable {n : ℕ}

/-! ### Möbius inversion and (14) -/

lemma sum_mobius (S : Finset (Fin n)) : ∀ W : Welfare n, ∑ T ∈ S.powerset, mobius W T = W S := by
  induction S using Finset.induction_on with
  | empty => intro W; simp [mobius]
  | insert a S ha ih =>
    intro W
    rw [Finset.sum_powerset_insert ha]
    have key : ∀ T ∈ S.powerset, mobius W (insert a T) =
        - mobius W T + mobius (fun R => W (insert a R)) T := by
      intro T hT
      have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
      unfold mobius
      rw [Finset.sum_powerset_insert haT, Finset.card_insert_of_notMem haT, ← Finset.sum_neg_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro R hR
        have hRT := Finset.card_le_card (Finset.mem_powerset.mp hR)
        rw [show T.card + 1 - R.card = (T.card - R.card) + 1 by omega, pow_succ]
        ring
      · apply Finset.sum_congr rfl
        intro R hR
        have haR : a ∉ R := fun h => haT (Finset.mem_powerset.mp hR h)
        rw [Finset.card_insert_of_notMem haR]
        congr 2
        omega
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_neg_distrib, ih W,
      ih (fun R => W (insert a R))]
    ring

lemma W_eq_sum_coalitionsIn (W : Welfare n) (h0 : W ∅ = 0) (T : Finset (Fin n)) :
    W T = ∑ T' ∈ coalitionsIn W T, mobius W T' := by
  rw [← sum_mobius T W]
  symm
  apply Finset.sum_subset
  · intro T' hT'
    unfold coalitionsIn at hT'
    exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hT').2
  · intro T' hT' hn
    unfold coalitionsIn coalitions at hn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hn
    by_cases hne : T'.Nonempty
    · by_contra hq
      exact hn ⟨hne, hq⟩ (Finset.mem_powerset.mp hT')
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      simp [mobius, h0]

lemma coalitionsIn_sub (W : Welfare n) {S X : Finset (Fin n)} (hX : X ⊆ S) :
    coalitionsIn W X = (coalitionsIn W S).filter (fun T => T ⊆ X) := by
  ext T
  unfold coalitionsIn
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hX⟩, h2⟩
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩

/-! ### Integer inclusion–exclusion coefficients on a family `𝒞` -/

/-- `ñ(T) = 1 - ∑_{T' ∈ 𝒞, T ⊊ T'} ñ(T')`, so that `∑_{T ∈ 𝒞, T'' ⊆ T} ñ(T) = 1` for `T'' ∈ 𝒞`. -/
def ncoef (𝒞 : Finset (Finset (Fin n))) (T : Finset (Fin n)) : ℤ :=
  1 - ∑ T' ∈ (𝒞.filter (fun T' => T ⊂ T')).attach, ncoef 𝒞 T'.1
termination_by n + 1 - T.card
decreasing_by
  have h := T'.2
  rw [Finset.mem_filter] at h
  have h1 := Finset.card_lt_card h.2
  have h2 : T'.1.card ≤ n := by
    have := Finset.card_le_univ T'.1
    simpa using this
  omega

lemma ncoef_sum (𝒞 : Finset (Finset (Fin n))) (T'' : Finset (Fin n)) (h : T'' ∈ 𝒞) :
    ∑ T ∈ 𝒞.filter (fun T => T'' ⊆ T), ncoef 𝒞 T = 1 := by
  have hsplit : 𝒞.filter (fun T => T'' ⊆ T) = insert T'' (𝒞.filter (fun T => T'' ⊂ T)) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hT, hs⟩
      by_cases he : T = T''
      · left; exact he
      · right; exact ⟨hT, Finset.ssubset_iff_subset_ne.mpr ⟨hs, Ne.symm he⟩⟩
    · rintro (rfl | ⟨hT, hs⟩)
      · exact ⟨h, Finset.Subset.refl _⟩
      · exact ⟨hT, hs.subset⟩
  rw [hsplit, Finset.sum_insert (by simp)]
  rw [ncoef]
  rw [Finset.sum_attach (𝒞.filter (fun T' => T'' ⊂ T')) (fun T' => ncoef 𝒞 T')]
  ring

/-- The swap identity behind (48). -/
lemma swap_sum (𝒞 : Finset (Finset (Fin n))) (h : Finset (Fin n) → ℝ)
    (P : Finset (Fin n) → Prop) [DecidablePred P] :
    ∑ T ∈ 𝒞, (ncoef 𝒞 T : ℝ) * ∑ T'' ∈ 𝒞.filter (fun T'' => T'' ⊆ T ∧ P T''), h T'' =
      ∑ T'' ∈ 𝒞.filter P, h T'' := by
  simp_rw [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T'' hT''
  by_cases hP : P T''
  · rw [if_pos hP]
    have : ∀ T ∈ 𝒞, (ncoef 𝒞 T : ℝ) * (if T'' ⊆ T ∧ P T'' then h T'' else 0) =
        (if T'' ⊆ T then (ncoef 𝒞 T : ℝ) else 0) * h T'' := by
      intro T _
      by_cases hs : T'' ⊆ T
      · simp [hs, hP]
      · simp [hs]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← Finset.sum_filter]
    rw [← Int.cast_sum, ncoef_sum 𝒞 T'' hT'']
    simp
  · rw [if_neg hP]
    apply Finset.sum_eq_zero
    intro T _
    simp [hP]

/-! ### Lemma 4 for the basis rules -/

lemma basis_unfold (g : Rule n) (W : Welfare n) (T : Finset (Fin n)) (i : Fin n)
    (S : Finset (Fin n)) : basisRule g W T i S = if T ⊆ S then
      (1 / mobius W T) * (g i T - ∑ T' ∈ ((coalitionsIn W T).erase T).attach,
        mobius W T'.1 * basisRule g W T'.1 i S) else 0 := by
  rw [basisRule]

lemma mem_erase_coal {W : Welfare n} {T : Finset (Fin n)} (T' : Finset (Fin n))
    (h : T' ∈ (coalitionsIn W T).erase T) : T' ⊂ T ∧ T' ∈ coalitions W := by
  rw [Finset.mem_erase] at h
  unfold coalitionsIn at h
  rw [Finset.mem_filter] at h
  exact ⟨Finset.ssubset_iff_subset_ne.mpr ⟨h.2.2, h.1⟩, h.2.1⟩

/-- Lemma 4, first part: `f^T(i,S) = f^T(i,T)` whenever `T ⊆ S`. -/
lemma basis_local (g : Rule n) (W : Welfare n) (i : Fin n) :
    ∀ T S : Finset (Fin n), T ⊆ S → basisRule g W T i S = basisRule g W T i T := by
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
    intro S hTS
    rw [basis_unfold g W T i S, basis_unfold g W T i T, if_pos hTS, if_pos (subset_refl T)]
    congr 2
    apply Finset.sum_congr rfl
    intro T' _
    have h := mem_erase_coal T'.1 T'.2
    rw [ih T'.1 h.1 S (h.1.subset.trans hTS), ih T'.1 h.1 T h.1.subset]

/-- Lemma 4, second part: `f^T(i,T) = 0` for `i ∉ T`. -/
lemma basis_out (g : Rule n) (W : Welfare n) (h0 : ∀ i S, i ∉ S → g i S = 0) (i : Fin n) :
    ∀ T : Finset (Fin n), i ∉ T → basisRule g W T i T = 0 := by
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
    intro hi
    rw [basis_unfold g W T i T, if_pos (subset_refl T), h0 i T hi]
    have : ∑ T' ∈ ((coalitionsIn W T).erase T).attach, mobius W T'.1 * basisRule g W T'.1 i T
        = 0 := by
      apply Finset.sum_eq_zero
      intro T' _
      have h := mem_erase_coal T'.1 T'.2
      rw [basis_local g W i T'.1 T h.1.subset, ih T'.1 h.1 (fun hh => hi (h.1.subset hh))]
      ring
    rw [this]; ring

/-- `G(k, X) = ∑_{T ∈ 𝒯(X)} q_T f^T(k, T)`. -/
noncomputable def G (g : Rule n) (W : Welfare n) (k : Fin n) (X : Finset (Fin n)) : ℝ :=
  ∑ T ∈ coalitionsIn W X, mobius W T * basisRule g W T k T

lemma rhs_eq_G (g : Rule n) (W : Welfare n) (k : Fin n) (S : Finset (Fin n)) :
    ∑ T ∈ coalitions W, mobius W T * basisRule g W T k S = G g W k S := by
  unfold G coalitionsIn
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hTS : T ⊆ S
  · rw [if_pos hTS, basis_local g W k T S hTS]
  · rw [if_neg hTS, basis_unfold, if_neg hTS, mul_zero]

/-- (43): for a contributing coalition `T`, `g(k,T) = G(k,T)`. -/
lemma rec_eq (g : Rule n) (W : Welfare n) (k : Fin n) (T : Finset (Fin n))
    (hT : T ∈ coalitions W) : g k T = G g W k T := by
  have hq : mobius W T ≠ 0 := by
    unfold coalitions at hT
    exact (Finset.mem_filter.mp hT).2.2
  have hTin : T ∈ coalitionsIn W T := by
    unfold coalitionsIn
    exact Finset.mem_filter.mpr ⟨hT, Finset.Subset.refl T⟩
  unfold G
  rw [← Finset.add_sum_erase _ _ hTin]
  rw [basis_unfold g W T k T, if_pos (subset_refl T)]
  have : ∑ x ∈ (coalitionsIn W T).erase T, mobius W x * basisRule g W x k x =
      ∑ T' ∈ ((coalitionsIn W T).erase T).attach, mobius W T'.1 * basisRule g W T'.1 k T := by
    rw [← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro T' _
    rw [basis_local g W k T'.1 T (mem_erase_coal T'.1 T'.2).1.subset]
  rw [this]
  field_simp
  ring

/-! ### Games with integer resource multiplicities -/

/-- Players on resource `r` for a profile over an arbitrary resource type. -/
def pl {R : Type} [DecidableEq R] (a : Fin n → Finset R) (r : R) : Finset (Fin n) :=
  Finset.univ.filter (fun k => r ∈ a k)

/-- A game whose resource `r` comes with `v r` identical copies: if `f` guarantees equilibria,
so does every such weighted game (Appendix A, the scaling coefficients `v_r`, p. 17). -/
lemma weighted_pne (W : Welfare n) (f : Welfare n → Rule n) (hpne : GuaranteesPNE {W} f)
    {R : Type} [Fintype R] [DecidableEq R] (v : R → ℕ)
    (A : Fin n → Finset (Finset R)) (hA : ∀ k, (A k).Nonempty) :
    ∃ a : Fin n → Finset R, (∀ k, a k ∈ A k) ∧ ∀ k, ∀ b ∈ A k,
      ∑ r ∈ b, (v r : ℝ) * f W k (pl (Function.update a k b) r) ≤
        ∑ r ∈ a k, (v r : ℝ) * f W k (pl a r) := by
  classical
  let C := (Σ r : R, Fin (v r)) ⊕ Fin 2
  let m := Fintype.card C
  have hm : 1 < m := by
    show 1 < Fintype.card ((Σ r : R, Fin (v r)) ⊕ Fin 2)
    rw [Fintype.card_sum]; simp
  let e : C ≃ Fin m := Fintype.equivFin C
  let inlE : (Σ r : R, Fin (v r)) ↪ C := ⟨Sum.inl, Sum.inl_injective⟩
  let lift : Finset R → Finset (Fin m) := fun s =>
    ((s.sigma (fun r => (Finset.univ : Finset (Fin (v r))))).map inlE).map e.toEmbedding
  let A' : Fin n → Finset (Finset (Fin m)) := fun k => (A k).image lift
  have hA' : ∀ k, (A' k).Nonempty := fun k => (hA k).image _
  obtain ⟨a', ha', hN⟩ := hpne m hm (fun _ => W) (fun _ => rfl) A' hA'
  have hpre : ∀ k, ∃ s ∈ A k, lift s = a' k := by
    intro k
    have := ha' k
    simp only [A', Finset.mem_image] at this
    exact this
  choose a ha hla using hpre
  have ha'eq : a' = fun k => lift (a k) := by funext k; exact (hla k).symm
  -- utility of a lifted profile
  have hU : ∀ (b : Fin n → Finset R) (k : Fin n),
      utility (fun _ => W) f (fun k => lift (b k)) k =
        ∑ r ∈ b k, (v r : ℝ) * f W k (pl b r) := by
    intro b k
    unfold utility
    have hpl : ∀ (r : R) (t : Fin (v r)),
        players (fun k => lift (b k)) (e (Sum.inl ⟨r, t⟩)) = pl b r := by
      intro r t; ext k'; simp [players, pl, lift, inlE]
    simp only [lift, Finset.sum_map]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro r _
    have h2 : ∀ t : Fin (v r), f W k (players (fun k => lift (b k)) (e (Sum.inl ⟨r, t⟩))) =
        f W k (pl b r) := fun t => by rw [hpl r t]
    refine (Finset.sum_congr rfl (fun t _ => h2 t)).trans ?_
    simp
  refine ⟨a, ha, fun k b hb => ?_⟩
  have hdev := hN k (lift b) (Finset.mem_image_of_mem lift hb)
  have hupd : Function.update a' k (lift b) = fun k' => lift (Function.update a k b k') := by
    funext k'
    by_cases hk : k' = k
    · subst hk; simp
    · rw [Function.update_of_ne hk, Function.update_of_ne hk, ha'eq]
  rw [hupd, ha'eq, hU, hU] at hdev
  simpa using hdev

/-! ### Counterexample 3 (p. 30) -/

section CX3

variable (S : Finset (Fin n)) (𝒞 : Finset (Finset (Fin n))) (i j : Fin n)

/-- Resources: `r₁, r₂` and, for each `T ∈ 𝒞`, `r₁ᵀ, r₂ᵀ`. -/
abbrev Res := Fin 2 ⊕ ({T // T ∈ 𝒞} × Fin 2)

/-- Multiplicities `v_{r₁} = v_{r₂} = 1`, `v_{r₁ᵀ} = v_{r₂ᵀ} = |ñ(T)|`. -/
def vw : Res 𝒞 → ℕ
  | Sum.inl _ => 1
  | Sum.inr p => (ncoef 𝒞 p.1.1).natAbs

/-- The fixture of a resource: `S` for `r₁, r₂`, `T` for `r₁ᵀ, r₂ᵀ`. -/
def base : Res 𝒞 → Finset (Fin n)
  | Sum.inl _ => S
  | Sum.inr p => p.1.1

def topB : Res 𝒞 → Bool
  | Sum.inl x => decide (x = 0)
  | Sum.inr p => decide (p.2 = 0 ∧ i ∈ p.1.1)

def botB : Res 𝒞 → Bool
  | Sum.inl x => decide (x = 1)
  | Sum.inr p => decide (p.2 = 1 ∧ i ∈ p.1.1)

def lftB : Res 𝒞 → Bool
  | Sum.inl x => decide (x = 0)
  | Sum.inr p => decide (j ∈ p.1.1 ∧
      ((p.2 = 0 ∧ ncoef 𝒞 p.1.1 < 0) ∨ (p.2 = 1 ∧ 0 < ncoef 𝒞 p.1.1)))

def rgtB : Res 𝒞 → Bool
  | Sum.inl x => decide (x = 1)
  | Sum.inr p => decide (j ∈ p.1.1 ∧
      ((p.2 = 0 ∧ 0 < ncoef 𝒞 p.1.1) ∨ (p.2 = 1 ∧ ncoef 𝒞 p.1.1 < 0)))

def fixB (k : Fin n) : Res 𝒞 → Bool
  | Sum.inl _ => decide (k ∈ S)
  | Sum.inr p => decide (k ∈ p.1.1)

def act (B : Res 𝒞 → Bool) : Finset (Res 𝒞) := Finset.univ.filter (fun r => B r = true)

lemma sum_res (F : Res 𝒞 → ℝ) :
    ∑ r, F r = F (Sum.inl 0) + F (Sum.inl 1) +
      ∑ T ∈ 𝒞.attach, (F (Sum.inr (T, 0)) + F (Sum.inr (T, 1))) := by
  rw [Fintype.sum_sum_type, Fin.sum_univ_two, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  rw [Finset.univ_eq_attach]

lemma perT (z : ℤ) (p : Prop) [Decidable p] (x y : ℝ) (hp : ¬p → x = y) :
    ((if p ∧ 0 < z then (z.natAbs : ℝ) * x else 0) +
      (if p ∧ z < 0 then (z.natAbs : ℝ) * y else 0)) -
    ((if p ∧ z < 0 then (z.natAbs : ℝ) * x else 0) +
      (if p ∧ 0 < z then (z.natAbs : ℝ) * y else 0)) = z * (x - y) := by
  by_cases h : p
  · rcases lt_trichotomy z 0 with hz | hz | hz
    · have : ((z.natAbs : ℕ) : ℝ) = -(z : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hz)]
      simp only [h, hz, true_and, not_lt.mpr hz.le, if_true, if_false, this]
      ring
    · subst hz; simp
    · have : ((z.natAbs : ℕ) : ℝ) = (z : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hz)]
      simp only [h, hz, true_and, not_lt.mpr hz.le, if_true, if_false, this]
      ring
  · simp [h, hp h]

end CX3

section CX3b

variable (S : Finset (Fin n)) (𝒞 : Finset (Finset (Fin n))) (i j : Fin n)
  (W : Welfare n) (f : Welfare n → Rule n)

/-- Share of player `p` on resource `r`, when the other strategic player `q` is present on `r`
iff `X r`. -/
noncomputable def Fsh (p q : Fin n) (X : Res 𝒞 → Bool) (r : Res 𝒞) : ℝ :=
  (vw 𝒞 r : ℝ) * f W p (if X r = true then base S 𝒞 r else (base S 𝒞 r).erase q)

lemma natAbs_neg' (z : ℤ) (hz : z < 0) : ((z.natAbs : ℕ) : ℝ) = -(z : ℝ) := by
  rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hz)]

lemma natAbs_pos' (z : ℤ) (hz : 0 < z) : ((z.natAbs : ℕ) : ℝ) = (z : ℝ) := by
  rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hz)]

lemma ite_erase (T : Finset (Fin n)) (x : Fin n) :
    (if x ∈ T then T else T.erase x) = T := by
  split_ifs with h
  · rfl
  · exact Finset.erase_eq_of_notMem h

lemma fin2_ne : ¬ ((0 : Fin 2) = 1) := by decide
lemma fin2_ne' : ¬ ((1 : Fin 2) = 0) := by decide

/-- `j` at `Top`: `U_j(T,R) - U_j(T,L)`. -/
lemma Kj_top (hjout : ∀ T ∈ 𝒞, j ∉ T → f W j T = f W j (T.erase i)) :
    ∑ r ∈ act 𝒞 (rgtB 𝒞 j), Fsh S 𝒞 W f j i (topB 𝒞 i) r -
      ∑ r ∈ act 𝒞 (lftB 𝒞 j), Fsh S 𝒞 W f j i (topB 𝒞 i) r =
    f W j (S.erase i) - f W j S +
      ∑ T ∈ 𝒞, (ncoef 𝒞 T : ℝ) * (f W j T - f W j (T.erase i)) := by
  unfold act
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, sum_res,
    ← Finset.sum_attach 𝒞]
  have h1 : ∀ T ∈ 𝒞.attach,
      ((if rgtB 𝒞 j (Sum.inr (T, 0)) = true then Fsh S 𝒞 W f j i (topB 𝒞 i) (Sum.inr (T, 0))
          else 0) -
        (if lftB 𝒞 j (Sum.inr (T, 0)) = true then Fsh S 𝒞 W f j i (topB 𝒞 i) (Sum.inr (T, 0))
          else 0)) +
      ((if rgtB 𝒞 j (Sum.inr (T, 1)) = true then Fsh S 𝒞 W f j i (topB 𝒞 i) (Sum.inr (T, 1))
          else 0) -
        (if lftB 𝒞 j (Sum.inr (T, 1)) = true then Fsh S 𝒞 W f j i (topB 𝒞 i) (Sum.inr (T, 1))
          else 0)) =
      (ncoef 𝒞 T.1 : ℝ) * (f W j T.1 - f W j (T.1.erase i)) := by
    rintro ⟨T, hT⟩ _
    simp only [rgtB, lftB, topB, Fsh, vw, base, fin2_ne, fin2_ne', true_and, false_and,
      and_false, or_false, false_or, decide_eq_true_eq, ite_erase]
    by_cases hj : j ∈ T
    · rcases lt_trichotomy (ncoef 𝒞 T) 0 with hz | hz | hz
      · simp [hj, hz, not_lt.mpr hz.le, natAbs_neg' _ hz]; ring
      · simp [hz]
      · simp [hj, hz, not_lt.mpr hz.le, natAbs_pos' _ hz]; ring
    · simp [hj, hjout T hT hj]
  rw [Finset.sum_congr rfl h1]
  simp only [rgtB, lftB, topB, Fsh, vw, base, fin2_ne, fin2_ne', decide_true, decide_false,
    if_true, if_false, Bool.false_eq_true, Nat.cast_one, one_mul]
  ring

/-- `j` at `Bottom`: `U_j(B,R) - U_j(B,L)`. -/
lemma Kj_bot (hjout : ∀ T ∈ 𝒞, j ∉ T → f W j T = f W j (T.erase i)) :
    ∑ r ∈ act 𝒞 (rgtB 𝒞 j), Fsh S 𝒞 W f j i (botB 𝒞 i) r -
      ∑ r ∈ act 𝒞 (lftB 𝒞 j), Fsh S 𝒞 W f j i (botB 𝒞 i) r =
    -(f W j (S.erase i) - f W j S +
      ∑ T ∈ 𝒞, (ncoef 𝒞 T : ℝ) * (f W j T - f W j (T.erase i))) := by
  unfold act
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, sum_res,
    ← Finset.sum_attach 𝒞]
  have h1 : ∀ T ∈ 𝒞.attach,
      ((if rgtB 𝒞 j (Sum.inr (T, 0)) = true then Fsh S 𝒞 W f j i (botB 𝒞 i) (Sum.inr (T, 0))
          else 0) -
        (if lftB 𝒞 j (Sum.inr (T, 0)) = true then Fsh S 𝒞 W f j i (botB 𝒞 i) (Sum.inr (T, 0))
          else 0)) +
      ((if rgtB 𝒞 j (Sum.inr (T, 1)) = true then Fsh S 𝒞 W f j i (botB 𝒞 i) (Sum.inr (T, 1))
          else 0) -
        (if lftB 𝒞 j (Sum.inr (T, 1)) = true then Fsh S 𝒞 W f j i (botB 𝒞 i) (Sum.inr (T, 1))
          else 0)) =
      -((ncoef 𝒞 T.1 : ℝ) * (f W j T.1 - f W j (T.1.erase i))) := by
    rintro ⟨T, hT⟩ _
    simp only [rgtB, lftB, botB, Fsh, vw, base, fin2_ne, fin2_ne', true_and, false_and,
      and_false, or_false, false_or, decide_eq_true_eq, ite_erase]
    by_cases hj : j ∈ T
    · rcases lt_trichotomy (ncoef 𝒞 T) 0 with hz | hz | hz
      · simp [hj, hz, not_lt.mpr hz.le, natAbs_neg' _ hz]; ring
      · simp [hz]
      · simp [hj, hz, not_lt.mpr hz.le, natAbs_pos' _ hz]; ring
    · simp [hj, hjout T hT hj]
  rw [Finset.sum_congr rfl h1, Finset.sum_neg_distrib]
  simp only [rgtB, lftB, botB, Fsh, vw, base, fin2_ne, fin2_ne', decide_true, decide_false,
    if_true, if_false, Bool.false_eq_true, Nat.cast_one, one_mul]
  ring

/-- `i` against `rgt`: `U_i(B,·) - U_i(T,·)`. -/
lemma Ki_rgt (hiout : ∀ T ∈ 𝒞, i ∉ T → f W i T = f W i (T.erase j)) :
    ∑ r ∈ act 𝒞 (botB 𝒞 i), Fsh S 𝒞 W f i j (rgtB 𝒞 j) r -
      ∑ r ∈ act 𝒞 (topB 𝒞 i), Fsh S 𝒞 W f i j (rgtB 𝒞 j) r =
    (f W i S - f W i (S.erase j) -
      ∑ T ∈ 𝒞, (ncoef 𝒞 T : ℝ) * (f W i T - f W i (T.erase j))) := by
  unfold act
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, sum_res,
    ← Finset.sum_attach 𝒞]
  have h1 : ∀ T ∈ 𝒞.attach,
      ((if botB 𝒞 i (Sum.inr (T, 0)) = true then Fsh S 𝒞 W f i j (rgtB 𝒞 j) (Sum.inr (T, 0))
          else 0) -
        (if topB 𝒞 i (Sum.inr (T, 0)) = true then Fsh S 𝒞 W f i j (rgtB 𝒞 j) (Sum.inr (T, 0))
          else 0)) +
      ((if botB 𝒞 i (Sum.inr (T, 1)) = true then Fsh S 𝒞 W f i j (rgtB 𝒞 j) (Sum.inr (T, 1))
          else 0) -
        (if topB 𝒞 i (Sum.inr (T, 1)) = true then Fsh S 𝒞 W f i j (rgtB 𝒞 j) (Sum.inr (T, 1))
          else 0)) =
      -((ncoef 𝒞 T.1 : ℝ) * (f W i T.1 - f W i (T.1.erase j))) := by
    rintro ⟨T, hT⟩ _
    simp only [rgtB, botB, topB, Fsh, vw, base, fin2_ne, fin2_ne', true_and, false_and,
      and_false, or_false, false_or, decide_eq_true_eq]
    by_cases hi : i ∈ T
    · by_cases hj : j ∈ T
      · rcases lt_trichotomy (ncoef 𝒞 T) 0 with hz | hz | hz
        · simp [hi, hj, hz, not_lt.mpr hz.le, natAbs_neg' _ hz]; ring
        · simp [hz]
        · simp [hi, hj, hz, not_lt.mpr hz.le, natAbs_pos' _ hz]; ring
      · simp [hi, hj, Finset.erase_eq_of_notMem hj]
    · simp [hi, hiout T hT hi]
  rw [Finset.sum_congr rfl h1]
  simp only [rgtB, botB, topB, Fsh, vw, base, fin2_ne, fin2_ne', decide_true, decide_false,
    if_true, if_false, Bool.false_eq_true, Nat.cast_one, one_mul]
  rw [Finset.sum_neg_distrib]; ring

/-- `i` against `lft`: `U_i(B,·) - U_i(T,·)`. -/
lemma Ki_lft (hiout : ∀ T ∈ 𝒞, i ∉ T → f W i T = f W i (T.erase j)) :
    ∑ r ∈ act 𝒞 (botB 𝒞 i), Fsh S 𝒞 W f i j (lftB 𝒞 j) r -
      ∑ r ∈ act 𝒞 (topB 𝒞 i), Fsh S 𝒞 W f i j (lftB 𝒞 j) r =
    -(f W i S - f W i (S.erase j) -
      ∑ T ∈ 𝒞, (ncoef 𝒞 T : ℝ) * (f W i T - f W i (T.erase j))) := by
  unfold act
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, sum_res,
    ← Finset.sum_attach 𝒞]
  have h1 : ∀ T ∈ 𝒞.attach,
      ((if botB 𝒞 i (Sum.inr (T, 0)) = true then Fsh S 𝒞 W f i j (lftB 𝒞 j) (Sum.inr (T, 0))
          else 0) -
        (if topB 𝒞 i (Sum.inr (T, 0)) = true then Fsh S 𝒞 W f i j (lftB 𝒞 j) (Sum.inr (T, 0))
          else 0)) +
      ((if botB 𝒞 i (Sum.inr (T, 1)) = true then Fsh S 𝒞 W f i j (lftB 𝒞 j) (Sum.inr (T, 1))
          else 0) -
        (if topB 𝒞 i (Sum.inr (T, 1)) = true then Fsh S 𝒞 W f i j (lftB 𝒞 j) (Sum.inr (T, 1))
          else 0)) =
      ((ncoef 𝒞 T.1 : ℝ) * (f W i T.1 - f W i (T.1.erase j))) := by
    rintro ⟨T, hT⟩ _
    simp only [lftB, botB, topB, Fsh, vw, base, fin2_ne, fin2_ne', true_and, false_and,
      and_false, or_false, false_or, decide_eq_true_eq]
    by_cases hi : i ∈ T
    · by_cases hj : j ∈ T
      · rcases lt_trichotomy (ncoef 𝒞 T) 0 with hz | hz | hz
        · simp [hi, hj, hz, not_lt.mpr hz.le, natAbs_neg' _ hz]; ring
        · simp [hz]
        · simp [hi, hj, hz, not_lt.mpr hz.le, natAbs_pos' _ hz]; ring
      · simp [hi, hj, Finset.erase_eq_of_notMem hj]
    · simp [hi, hiout T hT hi]
  rw [Finset.sum_congr rfl h1]
  simp only [lftB, botB, topB, Fsh, vw, base, fin2_ne, fin2_ne', decide_true, decide_false,
    if_true, if_false, Bool.false_eq_true, Nat.cast_one, one_mul]
  ring

end CX3b

lemma mem_act (𝒞 : Finset (Finset (Fin n))) (B : Res 𝒞 → Bool) (r : Res 𝒞) :
    r ∈ act 𝒞 B ↔ B r = true := by simp [act]

open Classical in
/-- Players on a resource of Counterexample 3. -/
lemma pl_cx3 (S : Finset (Fin n)) (𝒞 : Finset (Finset (Fin n))) (i j : Fin n) (hij : i ≠ j)
    (b : Fin n → Finset (Res 𝒞))
    (hbi : ∀ r ∈ b i, i ∈ base S 𝒞 r) (hbj : ∀ r ∈ b j, j ∈ base S 𝒞 r)
    (hfix : ∀ k, k ≠ i → k ≠ j → b k = act 𝒞 (fixB S 𝒞 k)) (r : Res 𝒞) :
    pl b r = (base S 𝒞 r).filter (fun k => (k = i → r ∈ b i) ∧ (k = j → r ∈ b j)) := by
  ext k
  simp only [pl, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hki : k = i
  · subst hki
    constructor
    · intro h; exact ⟨hbi r h, fun _ => h, fun h' => absurd h' hij⟩
    · rintro ⟨-, h, -⟩; exact h rfl
  by_cases hkj : k = j
  · subst hkj
    constructor
    · intro h; exact ⟨hbj r h, fun h' => absurd h' hki, fun _ => h⟩
    · rintro ⟨-, -, h⟩; exact h rfl
  rw [hfix k hki hkj, mem_act]
  simp only [hki, hkj, IsEmpty.forall_iff, and_true]
  cases r with
  | inl x => simp [fixB, base]
  | inr p => simp [fixB, base]

lemma pl_cx3_j (S : Finset (Fin n)) (𝒞 : Finset (Finset (Fin n))) (i j : Fin n) (hij : i ≠ j)
    (b : Fin n → Finset (Res 𝒞))
    (hbi : ∀ r ∈ b i, i ∈ base S 𝒞 r) (hbj : ∀ r ∈ b j, j ∈ base S 𝒞 r)
    (hfix : ∀ k, k ≠ i → k ≠ j → b k = act 𝒞 (fixB S 𝒞 k)) (r : Res 𝒞) (hr : r ∈ b j) :
    pl b r = if r ∈ b i then base S 𝒞 r else (base S 𝒞 r).erase i := by
  rw [pl_cx3 S 𝒞 i j hij b hbi hbj hfix r]
  ext k
  by_cases h : r ∈ b i
  · simp only [h, if_true, Finset.mem_filter]
    constructor
    · exact fun h' => h'.1
    · intro hk; exact ⟨hk, fun _ => trivial, fun _ => hr⟩
  · simp only [h, if_false, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hk, h1, -⟩; exact ⟨h1, hk⟩
    · rintro ⟨hki, hk⟩; exact ⟨hk, fun h' => absurd h' hki, fun _ => hr⟩

lemma pl_cx3_i (S : Finset (Fin n)) (𝒞 : Finset (Finset (Fin n))) (i j : Fin n) (hij : i ≠ j)
    (b : Fin n → Finset (Res 𝒞))
    (hbi : ∀ r ∈ b i, i ∈ base S 𝒞 r) (hbj : ∀ r ∈ b j, j ∈ base S 𝒞 r)
    (hfix : ∀ k, k ≠ i → k ≠ j → b k = act 𝒞 (fixB S 𝒞 k)) (r : Res 𝒞) (hr : r ∈ b i) :
    pl b r = if r ∈ b j then base S 𝒞 r else (base S 𝒞 r).erase j := by
  rw [pl_cx3 S 𝒞 i j hij b hbi hbj hfix r]
  ext k
  by_cases h : r ∈ b j
  · simp only [h, if_true, Finset.mem_filter]
    constructor
    · exact fun h' => h'.1
    · intro hk; exact ⟨hk, fun _ => hr, fun _ => trivial⟩
  · simp only [h, if_false, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hk, -, h1⟩; exact ⟨h1, hk⟩
    · rintro ⟨hkj, hk⟩; exact ⟨hk, fun _ => hr, fun h' => absurd h' hkj⟩

/-- Counterexample 3 (p. 30): a best-response cycle between `i` and `j`. -/
lemma cx3 (W : Welfare n) (f : Welfare n → Rule n) (hpne : GuaranteesPNE {W} f)
    (S : Finset (Fin n)) (𝒞 : Finset (Finset (Fin n))) (h𝒞 : ∀ T ∈ 𝒞, T ⊆ S)
    (i j : Fin n) (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j)
    (hjout : ∀ T ∈ 𝒞, j ∉ T → f W j T = f W j (T.erase i))
    (hiout : ∀ T ∈ 𝒞, i ∉ T → f W i T = f W i (T.erase j))
    (hJ : 0 < f W j (S.erase i) - f W j S +
      ∑ T ∈ 𝒞, (ncoef 𝒞 T : ℝ) * (f W j T - f W j (T.erase i)))
    (hI : 0 < f W i S - f W i (S.erase j) -
      ∑ T ∈ 𝒞, (ncoef 𝒞 T : ℝ) * (f W i T - f W i (T.erase j))) : False := by
  classical
  let A : Fin n → Finset (Finset (Res 𝒞)) := fun k =>
    if k = i then {act 𝒞 (topB 𝒞 i), act 𝒞 (botB 𝒞 i)}
    else if k = j then {act 𝒞 (lftB 𝒞 j), act 𝒞 (rgtB 𝒞 j)}
    else {act 𝒞 (fixB S 𝒞 k)}
  have hA : ∀ k, (A k).Nonempty := by
    intro k; simp only [A]; split_ifs <;> simp
  obtain ⟨a, ha, hN⟩ := weighted_pne W f hpne (vw 𝒞) A hA
  have hai := ha i
  have haj := ha j
  simp only [A, if_true, if_neg (Ne.symm hij), Finset.mem_insert, Finset.mem_singleton] at hai haj
  have hfix : ∀ k, k ≠ i → k ≠ j → a k = act 𝒞 (fixB S 𝒞 k) := by
    intro k hki hkj
    have := ha k
    simp only [A, hki, hkj, if_false, Finset.mem_singleton] at this
    exact this
  -- the four strategies keep `i`, `j` inside the fixtures
  have bT : ∀ r ∈ act 𝒞 (topB 𝒞 i), i ∈ base S 𝒞 r := by
    intro r hr; rw [mem_act] at hr
    cases r with
    | inl x => exact hi
    | inr p => simp only [topB, decide_eq_true_eq] at hr; exact hr.2
  have bB : ∀ r ∈ act 𝒞 (botB 𝒞 i), i ∈ base S 𝒞 r := by
    intro r hr; rw [mem_act] at hr
    cases r with
    | inl x => exact hi
    | inr p => simp only [botB, decide_eq_true_eq] at hr; exact hr.2
  have bL : ∀ r ∈ act 𝒞 (lftB 𝒞 j), j ∈ base S 𝒞 r := by
    intro r hr; rw [mem_act] at hr
    cases r with
    | inl x => exact hj
    | inr p => simp only [lftB, decide_eq_true_eq] at hr; exact hr.1
  have bR : ∀ r ∈ act 𝒞 (rgtB 𝒞 j), j ∈ base S 𝒞 r := by
    intro r hr; rw [mem_act] at hr
    cases r with
    | inl x => exact hj
    | inr p => simp only [rgtB, decide_eq_true_eq] at hr; exact hr.1
  -- utilities in closed form
  have Uj : ∀ (b : Fin n → Finset (Res 𝒞)) (X Y : Res 𝒞 → Bool),
      b i = act 𝒞 X → b j = act 𝒞 Y → (∀ r ∈ act 𝒞 X, i ∈ base S 𝒞 r) →
      (∀ r ∈ act 𝒞 Y, j ∈ base S 𝒞 r) →
      (∀ k, k ≠ i → k ≠ j → b k = act 𝒞 (fixB S 𝒞 k)) →
      ∑ r ∈ act 𝒞 Y, (vw 𝒞 r : ℝ) * f W j (pl b r) = ∑ r ∈ act 𝒞 Y, Fsh S 𝒞 W f j i X r := by
    intro b X Y hbX hbY hX hY hbf
    apply Finset.sum_congr rfl
    intro r hr
    rw [pl_cx3_j S 𝒞 i j hij b (hbX ▸ hX) (hbY ▸ hY) hbf r (hbY ▸ hr)]
    simp only [Fsh, hbX, mem_act]
  have Ui : ∀ (b : Fin n → Finset (Res 𝒞)) (X Y : Res 𝒞 → Bool),
      b i = act 𝒞 X → b j = act 𝒞 Y → (∀ r ∈ act 𝒞 X, i ∈ base S 𝒞 r) →
      (∀ r ∈ act 𝒞 Y, j ∈ base S 𝒞 r) →
      (∀ k, k ≠ i → k ≠ j → b k = act 𝒞 (fixB S 𝒞 k)) →
      ∑ r ∈ act 𝒞 X, (vw 𝒞 r : ℝ) * f W i (pl b r) = ∑ r ∈ act 𝒞 X, Fsh S 𝒞 W f i j Y r := by
    intro b X Y hbX hbY hX hY hbf
    apply Finset.sum_congr rfl
    intro r hr
    rw [pl_cx3_i S 𝒞 i j hij b (hbX ▸ hX) (hbY ▸ hY) hbf r (hbX ▸ hr)]
    simp only [Fsh, hbY, mem_act]
  have fixU : ∀ (k : Fin n) (c : Finset (Res 𝒞)), ∀ k', k' ≠ i → k' ≠ j →
      Function.update a k c k' = act 𝒞 (fixB S 𝒞 k') ∨ k' = k := by
    intro k c k' h1 h2
    by_cases h : k' = k
    · right; exact h
    · left; rw [Function.update_of_ne h]; exact hfix k' h1 h2
  have updj : ∀ Y : Res 𝒞 → Bool, ∀ k, k ≠ i → k ≠ j →
      Function.update a j (act 𝒞 Y) k = act 𝒞 (fixB S 𝒞 k) := by
    intro Y k h1 h2; rw [Function.update_of_ne h2]; exact hfix k h1 h2
  have updi : ∀ X : Res 𝒞 → Bool, ∀ k, k ≠ i → k ≠ j →
      Function.update a i (act 𝒞 X) k = act 𝒞 (fixB S 𝒞 k) := by
    intro X k h1 h2; rw [Function.update_of_ne h1]; exact hfix k h1 h2
  have Kjt := Kj_top S 𝒞 i j W f hjout
  have Kjb := Kj_bot S 𝒞 i j W f hjout
  have Kir := Ki_rgt S 𝒞 i j W f hiout
  have Kil := Ki_lft S 𝒞 i j W f hiout
  have uji : Function.update a j (act 𝒞 (rgtB 𝒞 j)) i = a i := Function.update_of_ne hij _ _
  have uji' : Function.update a j (act 𝒞 (lftB 𝒞 j)) i = a i := Function.update_of_ne hij _ _
  have uij : Function.update a i (act 𝒞 (botB 𝒞 i)) j = a j :=
    Function.update_of_ne (Ne.symm hij) _ _
  have uij' : Function.update a i (act 𝒞 (topB 𝒞 i)) j = a j :=
    Function.update_of_ne (Ne.symm hij) _ _
  rcases hai with hai | hai <;> rcases haj with haj | haj
  · -- (Top, L): j moves to R
    have hdev := hN j _ (show act 𝒞 (rgtB 𝒞 j) ∈ A j by simp [A, Ne.symm hij])
    rw [haj, Uj _ (topB 𝒞 i) (rgtB 𝒞 j) (uji.trans hai) (by simp) bT bR (updj _),
      Uj a (topB 𝒞 i) (lftB 𝒞 j) hai haj bT bL hfix] at hdev
    linarith
  · -- (Top, R): i moves to B
    have hdev := hN i _ (show act 𝒞 (botB 𝒞 i) ∈ A i by simp [A])
    rw [hai, Ui _ (botB 𝒞 i) (rgtB 𝒞 j) (by simp) (uij.trans haj) bB bR (updi _),
      Ui a (topB 𝒞 i) (rgtB 𝒞 j) hai haj bT bR hfix] at hdev
    linarith
  · -- (Bottom, L): i moves to T
    have hdev := hN i _ (show act 𝒞 (topB 𝒞 i) ∈ A i by simp [A])
    rw [hai, Ui _ (topB 𝒞 i) (lftB 𝒞 j) (by simp) (uij'.trans haj) bT bL (updi _),
      Ui a (botB 𝒞 i) (lftB 𝒞 j) hai haj bB bL hfix] at hdev
    linarith
  · -- (Bottom, R): j moves to L
    have hdev := hN j _ (show act 𝒞 (lftB 𝒞 j) ∈ A j by simp [A, Ne.symm hij])
    rw [haj, Uj _ (botB 𝒞 i) (lftB 𝒞 j) (uji'.trans hai) (by simp) bB bL (updj _),
      Uj a (botB 𝒞 i) (rgtB 𝒞 j) hai haj bB bR hfix] at hdev
    linarith

end CSPLemma7Aux

open CSPLemma7Aux in
theorem solution (n : ℕ) (hn : 1 < n) (W : Welfare n) (f : Welfare n → Rule n)
    (hbb : IsBudgetBalanced (f W) W) (hpne : GuaranteesPNE {W} f)
    (h0 : ∀ i S, i ∉ S → f W i S = 0) :
    ∀ S : Finset (Fin n), ∀ i ∈ S,
      f W i S = ∑ T ∈ coalitions W, mobius W T * basisRule (f W) W T i S := by
  have hW0 : W ∅ = 0 := by have := hbb ∅; simpa using this.symm
  have Gout : ∀ k X, k ∉ X → G (f W) W k X = 0 := by
    intro k X hk
    unfold G
    apply Finset.sum_eq_zero
    intro T hT
    have hTX : T ⊆ X := by unfold coalitionsIn at hT; exact (Finset.mem_filter.mp hT).2
    rw [basis_out (f W) W h0 k T (fun h => hk (hTX h)), mul_zero]
  suffices key : ∀ S : Finset (Fin n), ∀ k, f W k S = G (f W) W k S by
    intro S i _
    rw [rhs_eq_G]
    exact key S i
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro k
    by_cases hkS : k ∉ S
    · rw [h0 k S hkS, Gout k S hkS]
    push Not at hkS
    by_cases hS : S ∈ coalitions W
    · exact rec_eq (f W) W k S hS
    by_contra hne
    set 𝒞 := coalitionsIn W S with h𝒞def
    have h𝒞 : ∀ T ∈ 𝒞, T ⊆ S := by
      intro T hT; unfold coalitionsIn at hT; exact (Finset.mem_filter.mp hT).2
    have h𝒞coal : ∀ T ∈ 𝒞, T ∈ coalitions W := by
      intro T hT; unfold coalitionsIn at hT; exact (Finset.mem_filter.mp hT).1
    have h𝒞ss : ∀ T ∈ 𝒞, T ⊂ S := by
      intro T hT
      refine Finset.ssubset_iff_subset_ne.mpr ⟨h𝒞 T hT, ?_⟩
      rintro rfl; exact hS (h𝒞coal T hT)
    -- `G` through the family `𝒞`
    have hGsub : ∀ (x : Fin n) (X : Finset (Fin n)), X ⊆ S →
        G (f W) W x X = ∑ T'' ∈ 𝒞.filter (fun T'' => T'' ⊆ X),
          mobius W T'' * basisRule (f W) W T'' x T'' := by
      intro x X hX
      unfold G
      rw [coalitionsIn_sub W hX]
    -- (F1)
    have F1 : ∀ x, ∑ T ∈ 𝒞, (ncoef 𝒞 T : ℝ) * f W x T = G (f W) W x S := by
      intro x
      have e1 : ∀ T ∈ 𝒞, (ncoef 𝒞 T : ℝ) * f W x T = (ncoef 𝒞 T : ℝ) *
          ∑ T'' ∈ 𝒞.filter (fun T'' => T'' ⊆ T ∧ True),
            mobius W T'' * basisRule (f W) W T'' x T'' := by
        intro T hT
        rw [ih T (h𝒞ss T hT) x, hGsub x T (h𝒞 T hT)]
        congr 1
        apply Finset.sum_congr _ (fun _ _ => rfl)
        ext; simp
      rw [Finset.sum_congr rfl e1, swap_sum, hGsub x S (subset_refl S)]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext T; simp only [Finset.mem_filter, and_true]
      constructor
      · intro h; exact ⟨h, h𝒞 T h⟩
      · intro h; exact h.1
    -- (F2)
    have F2 : ∀ x, ∀ p ∈ S, ∑ T ∈ 𝒞, (ncoef 𝒞 T : ℝ) * f W x (T.erase p) = f W x (S.erase p) := by
      intro x p hp
      have e1 : ∀ T ∈ 𝒞, (ncoef 𝒞 T : ℝ) * f W x (T.erase p) = (ncoef 𝒞 T : ℝ) *
          ∑ T'' ∈ 𝒞.filter (fun T'' => T'' ⊆ T ∧ p ∉ T''),
            mobius W T'' * basisRule (f W) W T'' x T'' := by
        intro T hT
        have hTS := h𝒞ss T hT
        rw [ih _ (Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset p T) hTS) x,
          hGsub x _ ((Finset.erase_subset p T).trans (h𝒞 T hT))]
        congr 1
        apply Finset.sum_congr _ (fun _ _ => rfl)
        ext T''; simp only [Finset.mem_filter, Finset.subset_erase]
      rw [Finset.sum_congr rfl e1, swap_sum,
        ih _ (Finset.erase_ssubset hp) x, hGsub x _ (Finset.erase_subset p S)]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext T''
      simp only [Finset.mem_filter, Finset.subset_erase]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, h𝒞 T'' h1, h2⟩
      · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
    -- equal totals
    have hsumG : ∑ x ∈ S, G (f W) W x S = W S := by
      unfold G
      rw [Finset.sum_comm, W_eq_sum_coalitionsIn W hW0 S]
      apply Finset.sum_congr rfl
      intro T hT
      rw [← Finset.mul_sum]
      have h5 := lemma_5 n hn W (f W) hbb h0 T (h𝒞coal T hT) S
      have : ∑ x ∈ S, basisRule (f W) W T x T = ∑ x ∈ S, basisRule (f W) W T x S := by
        apply Finset.sum_congr rfl
        intro x _
        rw [basis_local (f W) W x T S (h𝒞 T hT)]
      rw [this, h5, unanimity, if_pos (h𝒞 T hT), mul_one]
    have hsum : ∑ x ∈ S, f W x S = ∑ x ∈ S, G (f W) W x S := by rw [hsumG, hbb S]
    obtain ⟨i, hi, hI⟩ : ∃ i ∈ S, G (f W) W i S < f W i S := by
      by_contra hc
      push Not at hc
      exact hne ((Finset.sum_eq_sum_iff_of_le hc).mp hsum k hkS)
    obtain ⟨j, hj, hJ⟩ : ∃ j ∈ S, f W j S < G (f W) W j S := by
      by_contra hc
      push Not at hc
      exact hne ((Finset.sum_eq_sum_iff_of_le hc).mp hsum.symm k hkS).symm
    have hij : i ≠ j := by rintro rfl; linarith
    have hjout : ∀ T ∈ 𝒞, j ∉ T → f W j T = f W j (T.erase i) := by
      intro T _ hjT
      rw [h0 j T hjT, h0 j _ (fun h => hjT (Finset.mem_of_mem_erase h))]
    have hiout : ∀ T ∈ 𝒞, i ∉ T → f W i T = f W i (T.erase j) := by
      intro T _ hiT
      rw [h0 i T hiT, h0 i _ (fun h => hiT (Finset.mem_of_mem_erase h))]
    apply cx3 W f hpne S 𝒞 h𝒞 i j hi hj hij hjout hiout
    · simp only [mul_sub, Finset.sum_sub_distrib]
      rw [F1 j, F2 j i hi]
      linarith
    · simp only [mul_sub, Finset.sum_sub_distrib]
      rw [F1 i, F2 i j hj]
      linarith
