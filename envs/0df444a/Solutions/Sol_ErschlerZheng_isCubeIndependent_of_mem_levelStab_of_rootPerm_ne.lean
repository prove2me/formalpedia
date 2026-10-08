-- Prove2me | solution 1 for ErschlerZheng.isCubeIndependent_of_mem_levelStab_of_rootPerm_ne
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T02:11:07.969423+00:00
-- url     : https://prove2.me/submissions/5bc13e99-cf69-41a7-8968-d924c9b4f394

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

section
/-!
# A13: Lemma 5.6 on `T_d` (p. 27)

`g_j` fixes the first `j` digits of every ray and moves digit `j` (Lean index) by the root
permutation of its section, which has no fixed point. In `x·g_n^{ε_n} ⋯ g_1^{ε_1}` the last factor
`g_1^{ε_1}` is the only one that moves digit `1`, so `ε_1 ∈ {0, 1}` is read off digit `1`; cancel
it and continue (the statement holds for every ray `x`).
-/

open scoped RightActions

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace SphericalCubeDev

variable {d : ℕ → ℕ}

theorem sph_one_smul (x : SphericalRay d) : x <• (1 : SphericalTreeAut d) = x := one_smul _ x

theorem length_sphericalRayPrefix (x : SphericalRay d) (n : ℕ) :
    (sphericalRayPrefix x n).1.length = n := by
  simp [sphericalRayPrefix]

theorem digit_eq (x : SphericalRay d) (h : SphericalTreeAut d) (n i : ℕ) (hi : i < n) :
    (x <• h).1 i = (sphericalRayPrefix x n <• h).1[i]'(by
      rw [length_sphericalVertex_smul, length_sphericalRayPrefix]; exact hi) := by
  have e := sphericalRayPrefix_smul_aux (MulOpposite.op h) x n
  have h1 : i < (sphericalRayPrefix (x <• h) n).1.length := by
    rw [length_sphericalRayPrefix]; exact hi
  rw [← getElem_sphericalRayPrefix (x <• h) n i h1]
  exact List.getElem_of_eq (congrArg Subtype.val e) h1

/-- `h` fixes every vertex of level `j`. -/
def FixLevel (j : ℕ) (h : SphericalTreeAut d) : Prop :=
  ∀ v : SphericalVertex d, v.1.length = j → v <• h = v

/-- `h` fixes the digits below `m` of every ray. -/
def FixDigits (m : ℕ) (h : SphericalTreeAut d) : Prop :=
  ∀ (x : SphericalRay d) (i : ℕ), i < m → (x <• h).1 i = x.1 i

theorem FixLevel.fixDigits {j : ℕ} {h : SphericalTreeAut d} (hh : FixLevel j h) :
    FixDigits j h := by
  intro x i hi
  rw [digit_eq x h j i hi]
  have e := hh (sphericalRayPrefix x j) (length_sphericalRayPrefix x j)
  rw [List.getElem_of_eq (congrArg Subtype.val e), getElem_sphericalRayPrefix]

theorem FixDigits.mono {m k : ℕ} {h : SphericalTreeAut d} (hh : FixDigits m h) (hkm : k ≤ m) :
    FixDigits k h := fun x i hi => hh x i (by omega)

theorem FixDigits.mul {m : ℕ} {g h : SphericalTreeAut d} (hg : FixDigits m g)
    (hh : FixDigits m h) : FixDigits m (g * h) := by
  intro x i hi
  rw [MulOpposite.op_mul, mul_smul]
  show (x <• g <• h).1 i = x.1 i
  rw [hh _ i hi, hg x i hi]

theorem FixDigits.one (m : ℕ) : FixDigits m (1 : SphericalTreeAut d) := by
  intro x i _; rw [sph_one_smul]

theorem FixDigits.pow {m : ℕ} {h : SphericalTreeAut d} (hh : FixDigits m h) (e : ℕ) :
    FixDigits m (h ^ e) := by
  induction e with
  | zero => exact FixDigits.one m
  | succ e ih => rw [pow_succ]; exact ih.mul hh

/-- The prefix of length `m + 1` is the prefix of length `m` followed by the letter `x_m`. -/
theorem sphericalRayPrefix_succ_eq (x : SphericalRay d) (m : ℕ) :
    sphericalRayPrefix x (m + 1) =
      sphericalAppend (sphericalRayPrefix x m) rfl
        (sphericalLetter (d := fun i => d (i + (sphericalRayPrefix x m).1.length))
          ⟨x.1 m, by simpa [length_sphericalRayPrefix] using x.2 m⟩) := by
  apply Subtype.ext
  show List.ofFn (fun i : Fin (m + 1) => x.1 i) = List.ofFn (fun i : Fin m => x.1 i) ++ [x.1 m]
  rw [List.ofFn_succ', List.concat_eq_append]
  rfl

/-- Digit `m` of `x·h`, for `h` fixing level `m`, is the root permutation of the section. -/
theorem digit_moved {m : ℕ} {h : SphericalTreeAut d} (hh : FixLevel m h) (x : SphericalRay d) :
    (x <• h).1 m = (rootPerm (sphericalSec h (sphericalRayPrefix x m))
      ⟨x.1 m, by simpa [length_sphericalRayPrefix] using x.2 m⟩ : ℕ) := by
  rw [digit_eq x h (m + 1) m (by omega)]
  set v := sphericalRayPrefix x m
  set j : Fin ((fun i => d (i + v.1.length)) 0) :=
    ⟨x.1 m, by simpa [v, length_sphericalRayPrefix] using x.2 m⟩
  set y := sphericalLetter (d := fun i => d (i + v.1.length)) j
  have hv : v <• h = v := hh v (length_sphericalRayPrefix x m)
  have hpre : (sphericalRayPrefix x (m + 1)) = sphericalAppend v rfl y :=
    sphericalRayPrefix_succ_eq x m
  -- `(v y)·h = (v·h)(y·h_v)`
  have hsplit : (sphericalAppend v rfl y <• h).1 = v.1 ++ (y <• sphericalSec h v).1 := by
    have hp : (v <• h).1 <+: (sphericalAppend v rfl y <• h).1 :=
      (sphericalVertex_smul_prefix_iff h _ _).2 (List.prefix_append _ _)
    rw [hv] at hp
    obtain ⟨t, ht⟩ := hp
    rw [← ht]
    congr 1
    show t = (sphericalDrop (sphericalAppend v rfl y <• h) v.1.length).1
    simp only [sphericalDrop]
    rw [← ht]
    simp
  have hlen1 : (y <• sphericalSec h v).1.length = 1 := by
    rw [length_sphericalVertex_smul]; simp [y, sphericalLetter]
  obtain ⟨k, hk⟩ := List.length_eq_one_iff.mp hlen1
  have hm : v.1.length = m := length_sphericalRayPrefix x m
  simp only [List.getElem_of_eq (congrArg Subtype.val (congrArg (· <• h) hpre)), hsplit]
  rw [List.getElem_append_right (by omega)]
  simp only [hk, hm, Nat.sub_self, List.getElem_cons_zero]
  have hk' : ((sphericalLetter j <• sphericalSec h (sphericalRayPrefix x m)) :
      SphericalVertex (fun i => d (i + v.1.length))).1 = [k] := hk
  simp [rootPerm, hk']

/-- `g_{a+n}^{ε_{a+n}} ⋯ g_{a+1}^{ε_{a+1}}`. -/
def F (g : ℕ → SphericalTreeAut d) (a n : ℕ) (ε : ℕ → ℕ) : SphericalTreeAut d :=
  ((List.range n).reverse.map fun i => g (a + i + 1) ^ ε (a + i + 1)).prod

theorem F_succ (g : ℕ → SphericalTreeAut d) (a n : ℕ) (ε : ℕ → ℕ) :
    F g a (n + 1) ε = F g (a + 1) n ε * g (a + 1) ^ ε (a + 1) := by
  unfold F
  rw [List.range_succ_eq_map, List.reverse_cons, List.map_append, List.prod_append,
    List.map_reverse, List.map_map, List.map_reverse]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, add_zero]
  congr 3
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.succ_eq_add_one]
  rw [show a + (i + 1) + 1 = a + 1 + i + 1 by omega]

theorem F_fix (g : ℕ → SphericalTreeAut d) (hfix : ∀ n, 1 ≤ n → FixLevel n (g n)) (a n : ℕ)
    (ε : ℕ → ℕ) : FixDigits (a + 1) (F g a n ε) := by
  unfold F
  induction n with
  | zero => exact FixDigits.one _
  | succ n ih =>
    rw [List.range_succ, List.reverse_append, List.map_append, List.prod_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact (((hfix _ (by omega)).fixDigits.pow _).mono (by omega)).mul ih

theorem core (g : ℕ → SphericalTreeAut d) (hfix : ∀ n, 1 ≤ n → FixLevel n (g n))
    (hmove : ∀ n, 1 ≤ n → ∀ x : SphericalRay d, (x <• g n).1 n ≠ x.1 n) :
    ∀ (n a : ℕ) (x : SphericalRay d) (ε ε' : ℕ → ℕ),
      (∀ j, a < j → j ≤ a + n → ε j ≤ 1 ∧ ε' j ≤ 1) →
      x <• F g a n ε = x <• F g a n ε' → ∀ j, a < j → j ≤ a + n → ε j = ε' j := by
  intro n
  induction n with
  | zero => intro a x ε ε' _ _ j h1 h2; omega
  | succ n ih =>
    intro a x ε ε' hb he j hj1 hj2
    rw [F_succ, F_succ, MulOpposite.op_mul, MulOpposite.op_mul, mul_smul, mul_smul] at he
    set z := x <• F g (a + 1) n ε
    set z' := x <• F g (a + 1) n ε'
    have hz : z.1 (a + 1) = x.1 (a + 1) := F_fix g hfix (a + 1) n ε x (a + 1) (by omega)
    have hz' : z'.1 (a + 1) = x.1 (a + 1) := F_fix g hfix (a + 1) n ε' x (a + 1) (by omega)
    have hdig0 : ∀ w : SphericalRay d, (w <• g (a + 1) ^ 0).1 (a + 1) = w.1 (a + 1) := by
      intro w; rw [pow_zero, sph_one_smul]
    have hdig1 : ∀ w : SphericalRay d, (w <• g (a + 1) ^ 1).1 (a + 1) ≠ w.1 (a + 1) := by
      intro w; rw [pow_one]; exact hmove _ (by omega) w
    have ha : ε (a + 1) = ε' (a + 1) := by
      have h1 := congrArg (fun w : SphericalRay d => w.1 (a + 1)) he
      change (z <• g (a + 1) ^ ε (a + 1)).1 (a + 1) = (z' <• g (a + 1) ^ ε' (a + 1)).1 (a + 1)
        at h1
      have b1 := (hb (a + 1) (by omega) (by omega)).1
      have b2 := (hb (a + 1) (by omega) (by omega)).2
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b1 with e1 | e1 <;>
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b2 with e2 | e2
      · rw [e1, e2]
      · exfalso; rw [e1, e2, hdig0, hz] at h1; exact hdig1 z' (by rw [← h1, hz'])
      · exfalso; rw [e1, e2, hdig0 z', hz'] at h1; exact hdig1 z (by rw [h1, hz])
      · rw [e1, e2]
    rcases (show j = a + 1 ∨ a + 1 < j by omega) with rfl | hj
    · exact ha
    · rw [ha] at he
      have hzz : z = z' := MulAction.injective (MulOpposite.op (g (a + 1) ^ ε' (a + 1))) he
      exact ih (a + 1) x ε ε' (fun j h1 h2 => hb j (by omega) (by omega)) hzz j hj (by omega)

theorem cubeProd_eq_F (g : ℕ → SphericalTreeAut d) (n : ℕ) (ε : ℕ → ℕ) :
    cubeProd g n ε = F g 0 n ε := by
  unfold cubeProd F
  simp only [zero_add]

end SphericalCubeDev

end ErschlerZheng
end

section
open scoped RightActions
set_option linter.unusedSimpArgs false
open ErschlerZheng
open SphericalCubeDev in
theorem solution (d : ℕ → ℕ) (hd : ∀ j, 2 ≤ d j)
    (G : Subgroup (SphericalTreeAut d)) (g : ℕ → SphericalTreeAut d)
    (_hgG : ∀ n, 1 ≤ n → g n ∈ G)
    (hstab : ∀ n, 1 ≤ n → ∀ v : SphericalVertex d, v.1.length = n → v <• g n = v)
    (hroot : ∀ n, 1 ≤ n → ∀ v : SphericalVertex d, v.1.length = n →
      ∀ j, rootPerm (sphericalSec (g n) v) j ≠ j) :
    IsCubeIndependent (rightOrbit G (sphericalOneRay d hd)) (fun _ => 1) g := by
  have hmove : ∀ n, 1 ≤ n → ∀ x : SphericalRay d, (x <• g n).1 n ≠ x.1 n := by
    intro n hn x
    rw [digit_moved (hstab n hn) x]
    intro e
    exact hroot n hn _ (length_sphericalRayPrefix x n) _ (Fin.ext e)
  intro n _ x _ ε ε' hb he j hj1 hj2
  rw [cubeProd_eq_F, cubeProd_eq_F] at he
  exact core g hstab hmove n 0 x ε ε' (fun j h1 h2 => hb j (by omega) (by omega)) he j hj1
    (by omega)
end
