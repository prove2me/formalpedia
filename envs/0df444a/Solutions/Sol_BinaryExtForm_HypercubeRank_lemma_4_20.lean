-- Prove2me | solution 1 for BinaryExtForm.HypercubeRank.lemma_4_20
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T19:01:29.798192+00:00
-- url     : https://prove2.me/submissions/8649e585-b5f0-4626-825a-7e3acafc8b17

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model

namespace BinaryExtForm.HypercubeRank.FiberProof

lemma binarization_convex {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) : Convex ℝ B := by
  obtain ⟨S,hS⟩ := hB.1
  rw [hS]
  exact convex_convexHull ℝ _

lemma binary_label {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) {p : Fin (d + 1) → ℝ}
    (hp : p ∈ B) (hb : IsBinaryY p) : ∃ m : ℕ, m ≤ k ∧ p 0 = m := by
  have hh : p 0 ∈ (fun p => p 0) '' {p | p ∈ B ∧ IsBinaryY p} := ⟨p,⟨hp,hb⟩,rfl⟩
  rw [hB.2.2.2] at hh
  exact hh

lemma binary_fiber_no_lt {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) {u v : Fin (d + 1) → ℝ}
    (hu : u ∈ B) (hv : v ∈ B) (hb : IsBinaryY u)
    (hy : yproj u = yproj v) : ¬ u 0 < v 0 := by
  intro hlt
  have hb' : IsBinaryY v := by
    intro i
    have heq : u i.succ = v i.succ := congrFun hy i
    rw [← heq]
    exact hb i
  obtain ⟨a,ha,hua⟩ := binary_label hB hu hb
  obtain ⟨b,hbnd,hvb⟩ := binary_label hB hv hb'
  have hab : a < b := by exact_mod_cast (show (a:ℝ)<b by simpa [hua,hvb] using hlt)
  have hdiff : 1 ≤ v 0-u 0 := by
    have hh : (a:ℝ)+1 ≤ b := by exact_mod_cast (show a+1≤b by omega)
    rw [hua,hvb]
    linarith
  let t : ℝ := 1 / (2*(v 0-u 0))
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; apply (div_le_iff₀ (by linarith : 0 < 2*(v 0-u 0))).mpr; linarith
  let p : Fin (d+1) → ℝ := (1-t) • u + t • v
  have hp : p ∈ B := binarization_convex hB hu hv (sub_nonneg.mpr ht1) ht.le (by ring)
  have hpy (i : Fin d) : p i.succ = u i.succ := by
    have hh : u i.succ = v i.succ := congrFun hy i
    simp only [p,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [← hh]
    ring
  have hpb : IsBinaryY p := by
    intro i
    rw [hpy]
    exact hb i
  obtain ⟨m,hm,hpm⟩ := binary_label hB hp hpb
  have hp0 : p 0 = u 0+1/2 := by
    simp only [p,Pi.add_apply,Pi.smul_apply,smul_eq_mul,t]
    field_simp
    ring
  have ham : a < m := by
    have hh : (a : ℝ) < m := by rw [← hpm,hp0,hua]; norm_num
    exact_mod_cast hh
  have hma : m < a+1 := by
    have hh : (m : ℝ) < (a : ℝ) + 1 := by rw [← hpm,hp0,hua]; norm_num
    exact_mod_cast hh
  omega

lemma binary_fiber_unique {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) {u v : Fin (d + 1) → ℝ}
    (hu : u ∈ B) (hv : v ∈ B) (hb : IsBinaryY u)
    (hy : yproj u = yproj v) : u = v := by
  have hb' : IsBinaryY v := by
    intro i
    have heq : u i.succ = v i.succ := congrFun hy i
    rw [← heq]
    exact hb i
  have hx : u 0 = v 0 := le_antisymm
    (le_of_not_gt (binary_fiber_no_lt hB hv hu hb' hy.symm))
    (le_of_not_gt (binary_fiber_no_lt hB hu hv hb hy))
  ext i
  refine Fin.cases hx (fun j => congrFun hy j) i

end BinaryExtForm.HypercubeRank.FiberProof

namespace BinaryExtForm.HypercubeRank.FiberProof

lemma cube_labeling {d : ℕ} (B : Set (Fin (d+1) → ℝ))
    (hB : IsHypercubeBinarization d B) :
    ∃ (p : (Fin d → Bool) → (Fin (d+1) → ℝ)) (e : (Fin d → Bool) ≃ Fin (2^d)),
      (∀ y, p y ∈ Set.extremePoints ℝ B) ∧
      (∀ y i, p y i.succ = if y i then 1 else 0) ∧
      (∀ y, p y 0 = ((e y).val : ℝ)) := by
  classical
  have hp_exists (y : Fin d → Bool) : ∃ p ∈ Set.extremePoints ℝ B,
      ∀ i, p i.succ = if y i then 1 else 0 := by
    have hy : (fun i => if y i then (1:ℝ) else 0) ∈
        {y : Fin d → ℝ | ∀ i, y i=0 ∨ y i=1} := by
      intro i
      cases y i <;> simp
    rw [← hB.2.1] at hy
    obtain ⟨p,hp,heq⟩ := hy
    exact ⟨p,hp,fun i => congrFun heq i⟩
  choose p hp hpy using hp_exists
  have hn_exists (y : Fin d → Bool) : ∃ m : ℕ, m < 2^d ∧ p y 0 = m := by
    have hh : p y 0 ∈ (fun p => p 0) '' Set.extremePoints ℝ B := ⟨p y,hp y,rfl⟩
    rw [hB.2.2] at hh
    obtain ⟨m,hm,heq⟩ := hh
    exact ⟨m,by omega,heq⟩
  choose n hn hpn using hn_exists
  let f : (Fin d → Bool) → Fin (2^d) := fun y => ⟨n y,hn y⟩
  have hsurj : Function.Surjective f := by
    intro m
    have hm : (m.val : ℝ) ∈ {t : ℝ | ∃ n : ℕ, n+1≤2^d ∧ t=n} :=
      ⟨m.val,by omega,rfl⟩
    rw [← hB.2.2] at hm
    obtain ⟨v,hv,hvm⟩ := hm
    have hvbin : IsBinaryY v := by
      have hh : yproj v ∈ yproj '' Set.extremePoints ℝ B := ⟨v,hv,rfl⟩
      rw [hB.2.1] at hh
      exact hh
    let y : Fin d → Bool := fun i => decide (v i.succ=1)
    have hycoord (i : Fin d) : (if y i then (1:ℝ) else 0) = v i.succ := by
      rcases hvbin i with hz|ho
      · simp [y,hz]
      · simp [y,ho]
    have hyp : yproj (p y) = yproj v := by
      ext i
      exact (hpy y i).trans (hycoord i)
    have hpbin : IsBinaryY (p y) := by
      intro i
      rw [hpy]
      cases y i <;> simp
    have hpv : p y = v := binary_fiber_unique hB.1 (hp y).1 hv.1 hpbin hyp
    refine ⟨y,?_⟩
    apply Fin.ext
    change n y = m.val
    have hh : (n y : ℝ) = (m.val : ℝ) := by
      rw [← hpn y,hpv]
      exact hvm
    exact_mod_cast hh
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_surjective_and_card f).mpr ⟨hsurj,by simp⟩
  exact ⟨p,Equiv.ofBijective f hbij,hp,hpy,hpn⟩

end BinaryExtForm.HypercubeRank.FiberProof



set_option autoImplicit false

namespace BinaryExtForm.HypercubeRank.DivisibilityProof

lemma predicate_piecewise_iff {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (P : (ι → Bool) → Prop)
    (hinv : ∀ i ∈ F, ∀ x b, P (Function.update x i b) ↔ P x)
    (z x : ι → Bool) : P (F.piecewise z x) ↔ P x := by
  revert hinv
  induction F using Finset.induction_on with
  | empty => intro _; simp
  | @insert i F hi ih =>
    intro hinv
    rw [Finset.piecewise_insert]
    exact (hinv i (Finset.mem_insert_self _ _) _ _).trans
      (ih (fun k hk => hinv k (Finset.mem_insert_of_mem hk)))

noncomputable def cubeSplit {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (u : {i // i ∈ F} → Bool) (w : {i // i ∉ F} → Bool) (i : ι) : Bool :=
  if hi : i ∈ F then u ⟨i, hi⟩ else w ⟨i, hi⟩

lemma free_coordinates_dvd_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset ι) (P : (ι → Bool) → Prop) [DecidablePred P]
    (hinv : ∀ i ∈ F, ∀ x b, P (Function.update x i b) ↔ P x) :
    2^F.card ∣ Fintype.card {x : ι → Bool // P x} := by
  classical
  let Q : ({i // i ∉ F} → Bool) → Prop := fun w => P (cubeSplit F (fun _ => false) w)
  have hsplit (u : {i // i ∈ F} → Bool) (w : {i // i ∉ F} → Bool) :
      P (cubeSplit F u w) ↔ Q w := by
    have he : F.piecewise (fun _ => false) (cubeSplit F u w) =
        cubeSplit F (fun _ => false) w := by
      ext i
      by_cases hi : i ∈ F <;> simp [Finset.piecewise, cubeSplit, hi]
    exact ((predicate_piecewise_iff F P hinv (fun _ => false) (cubeSplit F u w)).symm).trans
      (by rw [he])
  have hreconstruct (x : ι → Bool) :
      cubeSplit F (fun i => x i) (fun i => x i) = x := by
    ext i
    by_cases hi : i ∈ F <;> simp [cubeSplit, hi]
  let e : {x : ι → Bool // P x} ≃
      ({i // i ∈ F} → Bool) × {w : {i // i ∉ F} → Bool // Q w} := {
    toFun := fun x => ⟨(fun i => x.val i), ⟨(fun i => x.val i), by
      apply (hsplit (fun i => x.val i) (fun i => x.val i)).mp
      rw [hreconstruct]
      exact x.property⟩⟩
    invFun := fun z => ⟨cubeSplit F z.1 z.2.val, (hsplit z.1 z.2.val).mpr z.2.property⟩
    left_inv := by
      intro x
      apply Subtype.ext
      exact hreconstruct x.val
    right_inv := by
      rintro ⟨u,w⟩
      apply Prod.ext
      · funext i
        simp [cubeSplit, i.property]
      · apply Subtype.ext
        funext i
        simp [cubeSplit, i.property]
  }
  have hc := Fintype.card_congr e
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at hc
  exact ⟨Fintype.card {w : {i // i ∉ F} → Bool // Q w}, hc⟩

end BinaryExtForm.HypercubeRank.DivisibilityProof

namespace BinaryExtForm.HypercubeRank.DivisibilityProof

theorem divisibility_of_cube_labeling {d ℓ : ℕ} (B : Set (Fin (d+1) → ℝ))
    (α : Fin ℓ → ℕ) (hα : ∀ j, α j + 2 ≤ 2^d)
    (p : (Fin d → Bool) → (Fin (d+1) → ℝ))
    (e : (Fin d → Bool) ≃ Fin (2^d))
    (hp : ∀ y, p y ∈ Set.extremePoints ℝ B)
    (hy : ∀ y i, p y i.succ = if y i then 1 else 0)
    (hlabel : ∀ y, p y 0 = ((e y).val : ℝ)) :
    ∀ j, 2^fB B α ∣ α j + 1 := by
  classical
  intro j
  let F : Finset (Fin d) := Finset.univ.filter (fun i => ¬typeHit B α i)
  let P : (Fin d → Bool) → Prop := fun y => (e y).val ≤ α j
  have hinv : ∀ i ∈ F, ∀ y b, P (Function.update y i b) ↔ P y := by
    intro i hi y b
    have hfree : ¬typeHit B α i := (Finset.mem_filter.mp hi).2
    by_cases hsame : b = y i
    · subst b
      simp
    let z : Fin d → Bool := Function.update y i b
    have hdiff : DiffersOnlyAt (p z) (p y) i := by
      constructor
      · simp only [hy, z, Function.update_self]
        cases b <;> cases hyi : y i <;> simp_all
      · intro k hki
        rw [hy, hy]
        simp [z, Function.update_of_ne hki]
    change P z ↔ P y
    constructor
    · intro hz
      by_contra hy'
      apply hfree
      refine ⟨j, p z, hp z, p y, hp y, hdiff, ?_, ?_⟩
      · rw [hlabel]
        exact_mod_cast hz
      · rw [hlabel]
        have hn : α j + 1 ≤ (e y).val := by dsimp [P] at hy'; omega
        exact_mod_cast hn
    · intro hy'
      by_contra hz
      apply hfree
      refine ⟨j, p y, hp y, p z, hp z, ⟨hdiff.1.symm, fun k hk => (hdiff.2 k hk).symm⟩, ?_, ?_⟩
      · rw [hlabel]
        exact_mod_cast hy'
      · rw [hlabel]
        have hn : α j + 1 ≤ (e z).val := by dsimp [P] at hz; omega
        exact_mod_cast hn
  let ecut : {y : Fin d → Bool // P y} ≃ Fin (α j + 1) := {
    toFun := fun y => ⟨(e y.val).val, by have := y.property; dsimp [P] at this; omega⟩
    invFun := fun m => ⟨e.symm ⟨m.val, by have := hα j; have := m.isLt; omega⟩, by
      dsimp [P]
      simp only [Equiv.apply_symm_apply]
      have := m.isLt
      omega⟩
    left_inv := by
      intro y
      apply Subtype.ext
      apply e.injective
      simp only [Equiv.apply_symm_apply]
    right_inv := by
      intro m
      apply Fin.ext
      simp only [Equiv.apply_symm_apply]
  }
  have hc := Fintype.card_congr ecut
  simp only [Fintype.card_fin] at hc
  rw [← hc]
  change 2^F.card ∣ Fintype.card {y : Fin d → Bool // P y}
  exact free_coordinates_dvd_card F P hinv

end BinaryExtForm.HypercubeRank.DivisibilityProof

open BinaryExtForm.HypercubeRank

theorem solution {d ℓ : ℕ} (B : Set (Fin (d + 1) → ℝ)) (hB : IsHypercubeBinarization d B)
    (α : Fin ℓ → ℕ) (hα : ∀ j, α j + 2 ≤ 2 ^ d) :
    ∀ j, 2 ^ fB B α ∣ α j + 1 := by
  obtain ⟨p,e,hp,hy,hlabel⟩ := FiberProof.cube_labeling B hB
  exact DivisibilityProof.divisibility_of_cube_labeling B α hα p e hp hy hlabel
