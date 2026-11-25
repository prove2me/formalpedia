-- Prove2me | solution 1 for DetDLP.d2_terminal_greedy_poly
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T05:23:21.606727+00:00
-- url     : https://prove2.me/submissions/c291a1a4-d169-474a-98ac-0258bce2b8e6

import Definitions.Def_DetDLP_D2_Greedy
import Theorems.Thm_Groundwork_PolyT_pow_unary
import Theorems.Thm_Groundwork_PolyT_mod
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_Unary_of_length

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 3000
open Groundwork Groundwork.PolyT DetDLP DetDLP_W1_Queries DetDLP.D2.Greedy
attribute [local fun_prop] PolyT.comp PolyT.const PolyT.fst PolyT.snd PolyT.prodMk
  PolyT.map PolyT.sum PolyT.count PolyT.mul PolyT.mod PolyT.div PolyT.flatMap PolyT.filter PolyT.length
  P2M_Groundwork_PolyT_cond__4c673073da15 P2M_Groundwork_PolyT_cons__3a60f43a3b86
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219
  first_poly more_poly w5_M6Sort.encode_poly

section
variable {A B : Type} [Enc A] [Enc B]
@[local fun_prop] private theorem factP {p : A → List ℕ} {r k u v : A → ℕ}
    (hp : PolyT p) (hr : PolyT r) (hk : PolyT k) (hu : PolyT u) (hv : PolyT v) :
    PolyT (fun x => factor (p x) (r x) (k x) (u x) (v x)) := by
  unfold factor; fun_prop

@[local fun_prop] private theorem totP {l : A → List B} {f : A → B → ℕ}
    (hl : PolyT l) (hf : PolyT fun z : A × B => f z.1 z.2) : PolyT fun x => total (l x) (f x) :=
  PolyT.sum (PolyT.map hf hl)

@[local fun_prop] private theorem energyP {p places hosts : A → List ℕ} {q w v : A → ℕ} {es : A → List Edge}
    (hp : PolyT p) (hk : PolyT places) (hh : PolyT hosts) (hq : PolyT q) (hw : PolyT w) (hv : PolyT v)
    (he : PolyT es) : PolyT (fun x => energy (p x) (q x) (es x) (places x) (hosts x) (w x) (v x)) := by
  unfold energy edgeCost legCost; fun_prop

private theorem best_mem (cost : ℕ → ℕ) (l : List ℕ) (a : ℕ) :
    let n := l.foldl (fun i j => if cost j < cost i then j else i) a
    n = a ∨ n ∈ l := by
  induction l generalizing a with
  | nil => exact Or.inl rfl
  | cons b l ih =>
    simp only [List.foldl_cons,List.mem_cons]
    split
    · have h := ih b; tauto
    · have h := ih a; tauto

@[local fun_prop] private theorem bestP {l : A → List ℕ} {f : A → ℕ → ℕ}
    (hl : PolyT l) (hf : PolyT fun z : A × ℕ => f z.1 z.2) : PolyT fun x => best (f x) (l x) := by
  unfold best
  apply PolyT.foldl_add hl (PolyT.const 0) (g := fun x s e => if f x e < f x s then e else s)
  · fun_prop
  obtain ⟨t,ht,_,hb⟩ := len_bound hl
  refine ⟨t, ht, fun x c e he => ?_⟩
  split <;> have h := (len_le_of_mem he).trans (hb x) <;> omega

@[local fun_prop] private theorem maxP {l : A → List B} {f : A → B → ℕ}
    (hl : PolyT l) (hf : PolyT fun z : A × B => f z.1 z.2) : PolyT fun x => maxOn (l x) (f x) := by
  unfold D2.Greedy.maxOn
  have h := PolyT.map hf hl
  apply PolyT.foldl_add h (PolyT.const 0) (g := fun _ s e => max s e)
  · fun_prop
  obtain ⟨t,ht,_,hb⟩ := len_bound h
  refine ⟨t, ht, fun x c e he => ?_⟩
  have := (len_le_of_mem he).trans (hb x)
  rcases le_total c e with h|h <;> simp [max_eq_left,max_eq_right,h] <;> omega

@[local fun_prop] private theorem solveP {vs pal ps hs : A → List ℕ} {es : A → List Edge}
    (hvs : PolyT vs) (hpal : PolyT pal) (hps : PolyT ps) (hhs : PolyT hs) (hes : PolyT es) :
    PolyT fun x => solve (vs x) (pal x) (ps x) (hs x) (es x) := by
  unfold solve
  apply PolyT.foldl_add hvs (PolyT.const [])
  · fun_prop
  obtain ⟨t,ht,_,hb⟩ := len_bound hpal
  refine ⟨fun n => t n + (len (0:ℕ)+2), ht.add (PB.const _), fun x s e he => ?_⟩
  dsimp only
  generalize h : best _ (pal x) = j
  have hj : j = 0 ∨ j ∈ pal x := by rw [← h]; apply best_mem
  have h1 := len_append s [j]
  simp only [len_cons,len_nil] at h1
  rcases hj with rfl|hm
  · omega
  · have := (len_le_of_mem hm).trans (hb x); omega

private theorem bounded_range {n : A → ℕ} {l : A → List B} (hn : PolyT n) (hl : PolyT l)
    (hb : ∀ x, n x ≤ (l x).length) : PolyT fun x => List.range (n x) := by
  apply PolyT.range
  apply (Unary.of_length (PolyT.take hn hl)).congr
  intro x; simp [List.length_take, min_eq_left (hb x)]

private theorem pow_range {n : A → ℕ} {l : A → List B} (hn : PolyT n) (hl : PolyT l)
    (hb : ∀ x, n x ≤ (l x).length) : PolyT fun x => (List.range (n x)).map fun i => 64^i := by
  let cap (x : A) (i : ℕ) := ((l x).take i).length
  have hp : PolyT (fun z : A × ℕ => 64 ^ cap z.1 z.2) := by
    apply PolyT.pow_unary (PolyT.const _)
    apply Unary.of_length; fun_prop
  apply (PolyT.map (f := fun x i => 64 ^ cap x i) hp (bounded_range hn hl hb)).congr
  intro x; apply List.map_congr_left; intro i hi
  simp [cap, min_eq_left ((List.mem_range.mp hi).le.trans (hb x))]
end

theorem solution : PolyT run := by
  unfold run third second lastField
  have decP {A : Type} [Enc A] {f : A → W} (hf : PolyT f) : PolyT fun x => w5_M6Sort.decode (f x) :=
    PolyT.comp w5_M6Sort.decode_poly hf
  have oriP {A : Type} [Enc A] {s : A → W} {ep : A → List ℕ} {i : A → ℕ}
      (hs : PolyT s) (he : PolyT ep) (hi : PolyT i) : PolyT fun x => oriented (s x) (ep x) (i x) := by
    unfold oriented; fun_prop
  apply w5_M6Sort.encode_poly
  apply PolyT.flatMap
  · apply PolyT.map
    · fun_prop
    apply solveP
    · apply PolyT.range; apply Unary.of_length; fun_prop
    · apply PolyT.range; apply Unary.of_length; fun_prop
    · apply pow_range (l := fun z => first (more (more z.1))) (by fun_prop) (by fun_prop); exact fun _ => min_le_right ..
    · apply decP; fun_prop
    · apply PolyT.map
      · apply oriP <;> first | apply decP; fun_prop | fun_prop
      · apply bounded_range _ (decP (f := fun z => first (more (more (more (first z.1))))) (by fun_prop))
        · intro x; exact Nat.div_le_self ..
        · apply PolyT.div (PolyT.length (decP (by fun_prop))) (PolyT.const _)
  · apply pow_range (l := fun z => first (more (more z))) (by fun_prop) (by fun_prop); exact fun _ => min_le_right ..
